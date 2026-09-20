/**
 * Bidirectional type checking.
 *
 * `infer` synthesizes a type from a term; `check` verifies one against an
 * expected type. Nothing fails halfway: a term that does not check still yields
 * a type -- `TBad` where nothing better is known -- and `TBad` relates to
 * everything, so one mistake is reported once rather than at every later use.
 *
 * Elaboration happens here rather than in a pass of its own. A `fn` binds type
 * parameters that scope over its body, and the context *is* that scope, so a
 * type written inside a term can only be elaborated when checking reaches it.
 *
 * EVars come from exactly one place: instantiating a polymorphic callee at an
 * application. Nothing else invents one -- in particular an unannotated
 * parameter does not, which is why a bare `fn` is checkable but not inferable.
 */

import {
  type Diagnostic,
  type Position,
  reportError,
} from "../diagnostics/diagnostic.ts";
import {
  bindingHint,
  type BindingIdent,
  type MatchArm,
  type Program,
  type TermNode,
} from "../syntax/ast.ts";
import { Context } from "./context.ts";
import { type DataCtorInfo, Declarations } from "./context.ts";
import { ctorFieldsAt, Elaborator } from "./elaborate.ts";
import { Subtyper, type Verdict } from "./subtype.ts";
import {
  badUnder,
  closeFrom,
  completePattern,
  FVar,
  impossible,
  mkLevel,
  openMany,
  openWith,
  TFun,
  TMissing,
  TUnknown,
  type Type,
  type TypePattern,
  typeToString,
} from "./types.ts";

export class Checker {
  readonly declarations = new Declarations();
  readonly context = new Context(this.declarations);
  readonly diagnostics: Diagnostic[] = [];
  readonly elaborator: Elaborator;
  readonly subtyper: Subtyper;

  constructor() {
    this.elaborator = new Elaborator(
      this.declarations,
      this.context,
      this.diagnostics,
    );
    this.subtyper = new Subtyper(this.context, this.diagnostics);
  }

  /**
   * Builtins, then the program's declarations, then constructors, then the one
   * term they all serve.
   */
  checkProgram(program: Program): Type {
    this.elaborator.seedBuiltins();
    this.elaborator.elaborateDeclarations(program.decls);
    this.elaborator.seedConstructors();
    return this.infer(program.term);
  }

  #report(message: string, at: Position, width = 1): Diagnostic {
    const diagnostic = reportError(message, at, width);
    this.diagnostics.push(diagnostic);
    return diagnostic;
  }

  /**
   * Report a verdict other than `yes`, each in its own words.
   *
   * Only what an *ask* came to. What the subtyper recorded on the way -- a
   * widened bound, a refused constraint, a settled type argument -- it says
   * itself, into the same array: whether such a step was sound is known there
   * and not here.
   */
  #reportVerdict(
    verdict: Verdict,
    actual: Type,
    expected: TypePattern,
    at: Position,
  ): void {
    const found = typeToString(actual);
    const wanted = typeToString(expected);
    switch (verdict) {
      case true:
        return;
      case false:
        this.#report(`expected ${wanted}, found ${found}`, at);
        return;
      // Not absent: the fuel ran out. The checker's limit, not the program's
      // mistake, so not "found X, expected Y".
      case undefined:
        this.#report(
          `gave up comparing ${found} with ${wanted}: too deeply nested`,
          at,
        );
        return;
    }
  }

  // ---------------------------------------------------------------- checking

  /**
   * Check a term against what is known of its type, and answer with the type
   * it has. One procedure: `expected` is a *pattern*, so it may say everything
   * about the type, nothing at all, or anything in between. Inference is the
   * case where it says nothing.
   *
   * The answer is in general neither the pattern nor the term's own type, but
   * the pattern's shape with the term's content in its missing parts, which is
   * what `coerce` produces: the least supertype of the one matching the other,
   * reported once if there is none. On a type written in full the two agree --
   * a complete pattern matches only itself.
   *
   * This is nearly the only way a type meets an expected one, and every rule
   * meets it here, at the same term and the same position. What is left beside
   * it is a written type argument against its declared bound, a relation
   * rather than a coercion, which asks `isSubtype` directly.
   */
  check(term: TermNode, expected: TypePattern): Type {
    // Nothing comes back but the type: a cast that could not reach some part
    // has said so already, in that part's own words, which is what it is given
    // the position for.
    const coerce = (actual: Type) =>
      this.subtyper.upcast(actual, expected, term.at);

    switch (term.kind) {
      // The forms with a rule of their own: each pushes the pattern *inward*
      // rather than synthesizing and comparing at the end, which is the only
      // way an unannotated parameter ever gets a type.
      case "Abs":
        return coerce(this.#checkAbs(term, expected));
      case "Match":
        return coerce(this.#checkMatch(term, expected));
      case "App":
        return coerce(this.#applyCall(term, expected));
      // The two forms with nothing to push inward: a name already has a type
      // and a type application already says what it is. They synthesize, and
      // the pattern is applied afterwards.
      case "Var":
        return coerce(this.#inferVar(term));
      case "TypeApp":
        return coerce(this.#inferTypeApp(term));
      // The one form that coerces nowhere. A `let` hands the pattern to its
      // body and the body's own `check` is where it is met, so coercing the
      // answer again would only ask a settled question twice.
      case "Let":
        return this.#checkLet(term, expected);
      case "LetRec":
        return this.#checkLetRec(term, expected);
    }
  }

  /** Check against nothing, which is to synthesize. */
  infer(term: TermNode): Type {
    return this.check(term, TMissing);
  }

  /**
   * A lambda, against whatever the pattern says of it.
   *
   * The pattern is taken as written, not exposed: nothing has type
   * `X <: (Bool) -> Bool` but an `X`, so promoting to the bound would accept
   * any function of that shape where an `X` was asked for. Anything but a
   * literal arrow of the same quantifier arity demands nothing of the parts.
   *
   * Every part is taken from the pattern where it has one and from the term
   * otherwise, and nothing in between relates anything: a disagreement with
   * the pattern is the lambda having the wrong type, which the coercion in
   * `check` says once, over the whole arrow.
   */
  #checkAbs(
    term: Extract<TermNode, { kind: "Abs" }>,
    expected: TypePattern,
  ): Type {
    const wanted = expected.kind === "TFun" &&
        expected.typeParams.length === term.typeParams.length
      ? expected
      : undefined;

    const type = this.context.inScope((mark) => {
      // Decided before any of them is in scope, the way the parameters below
      // are: bounds are parallel, so one may name an enclosing binder but
      // never a member of its own group.
      const binders = this.elaborator.bindTypeParams(
        term.typeParams,
        term.typeParams.map((declared, j) => {
          if (declared.bound !== undefined) {
            return this.elaborator.elaborateType(declared.bound);
          }
          // Top where there is no pattern, which is what an unbounded type
          // parameter means anyway. The one place this rule and the parameter
          // rule below differ, and the whole of the difference: a bound left
          // unsaid has a sound reading and a parameter type does not.
          //
          // A bound the pattern reaches only in part could take `unknown` too,
          // assuming less of a type variable being safe. More precise and
          // worse: two type parameters that read the same in the source would
          // answer differently for a reason an author cannot see.
          return completePattern(
            wanted?.typeParams[j]?.bound ?? TUnknown,
            () => {
              const name = bindingHint(declared.name);
              return badUnder(this.#report(
                `cannot infer a bound for ${name}: write it, or use this ` +
                  `function where its bounds are known`,
                declared.name.at,
                name.length,
              ));
            },
          );
        }),
      );
      // One variable per binder, in order, so the group occupies exactly the
      // levels from the mark on.
      const opened = binders.map((binder, j) =>
        FVar(mkLevel(mark + j), binder.hint)
      );

      this.#reportDuplicateBinders(
        term.params.map((param) => param.name),
        "parameter list",
      );
      // Every parameter is settled before any name is pushed, so one list
      // binds simultaneously: an annotation may not see a name its own list
      // binds, and `fn [A](A: A, y: A)` resolves both `A`s to the type
      // variable. One per parameter the *term* wrote, whatever the pattern's
      // arity.
      const params = term.params.map((param, j) => {
        // What is written wins whole and unconditionally, including where it
        // disagrees with the pattern: the body is typed against what the
        // author wrote. Relating the two here would buy a message at the
        // parameter and pay for it by discarding the annotation -- the one
        // thing this rule promises to keep.
        if (param.annotation !== undefined) {
          return this.elaborator.elaborateType(param.annotation);
        }
        // A parameter the pattern does not reach is one it says nothing about,
        // which is what a missing part means -- so it is asked for like any
        // other rather than standing `<bad>`, which would claim something was
        // supplied. No pattern at all is that case for every parameter at
        // once, and needs no arm of its own: opening a missing part leaves it
        // missing.
        return completePattern(
          openMany<unknown>(wanted?.params[j] ?? TMissing, opened),
          () => {
            const name = bindingHint(param.name);
            return badUnder(this.#report(
              `cannot infer a type for ${name}: annotate it, or use this ` +
                `function where its parameter types are known`,
              param.name.at,
              name.length,
            ));
          },
        );
      });
      for (const [j, param] of term.params.entries()) {
        this.context.pushTermVar(
          params[j] ?? impossible("one type per written parameter"),
          param.name.text,
        );
      }

      const result = this.check(
        term.body,
        openMany(wanted?.result ?? TMissing, opened),
      );

      return TFun(
        binders,
        params.map((param) => closeFrom(param, mark)),
        closeFrom(result, mark),
      );
    });
    this.context.assertClosed("function", [type]);
    return type;
  }

  /** Report a name bound twice in one group: a parameter list, a pattern, a `def` run. */
  #reportDuplicateBinders(
    binders: readonly BindingIdent[],
    what: string,
  ): void {
    const seen = new Set<string>();
    for (const binder of binders) {
      // A wildcard is not in the running: it binds no name to collide.
      const name = binder.text;
      if (name === undefined) continue;
      if (seen.has(name)) {
        this.#report(
          `${name} is bound twice in one ${what}`,
          binder.at,
          name.length,
        );
      }
      seen.add(name);
    }
  }

  #checkLet(
    term: Extract<TermNode, { kind: "Let" }>,
    expected: TypePattern,
  ): Type {
    const result = this.context.inScope(() => {
      // Ascribed or synthesized. An annotation is what the bound term is
      // checked against *and* what the binding gets: the two agree, a complete
      // pattern matching only itself, and the annotation is what this binding
      // promises to keep.
      let bound: Type;
      if (term.annotation === undefined) {
        bound = this.infer(term.bound);
      } else {
        bound = this.elaborator.elaborateType(term.annotation);
        this.check(term.bound, bound);
      }
      this.context.pushTermVar(bound, term.name.text);
      return this.check(term.body, expected);
    });
    // With no dependent types a `let` body's type cannot mention the binding,
    // but say so out loud.
    this.context.assertClosed("let", [result]);
    return result;
  }

  /**
   * A run of `def`s, all of them in scope for all of the bodies -- or as much
   * of that as can be had without inventing a type nobody wrote.
   *
   * An annotated `def` is visible to the whole group, its signature being a
   * thing the author supplied rather than a thing the checker must find. An
   * unannotated one behaves like a `let`: visible once it is checked, and
   * `unknown` inside its own body. That is not a stand-in for the type it will
   * turn out to have -- it is the honest statement that nothing is known of
   * this binding yet, so it may be handed on as a value and may not be called.
   * A recursive use is refused at the call, where the recursion is.
   *
   * `unknown` and not `<bad>` for a reason the types enforce: `badUnder` takes
   * the diagnostic that licenses it, so a bad entry would mean reporting once
   * at the push, for a binding nothing may go on to mention. The report belongs
   * at each use, and `unknown` is what puts it there.
   *
   * A parameter left bare is settled before any of this, the parser having
   * stood a `MissingParamType` in its place, so nothing here has a case for it:
   * the def keeps whatever signature it wrote and the parameter stands `bad`.
   *
   * Order follows from that. Signatures first, so an annotated body may name
   * any member; then the unannotated ones, each replacing its own entry in
   * place once its type is known; then the annotated bodies. Nothing is ever
   * repushed at a different level, so no `FVar` already elaborated goes stale.
   */
  #checkLetRec(
    term: Extract<TermNode, { kind: "LetRec" }>,
    expected: TypePattern,
  ): Type {
    this.#reportDuplicateBinders(term.defs.map((def) => def.name), "def group");

    const result = this.context.inScope(() => {
      const signatures = new Map<number, Type>();
      for (const [index, def] of term.defs.entries()) {
        if (def.annotation === undefined) continue;
        const signature = this.elaborator.elaborateType(def.annotation);
        signatures.set(index, signature);
        this.context.pushTermVar(signature, def.name.text);
      }

      for (const [index, def] of term.defs.entries()) {
        if (signatures.has(index)) continue;
        const level = this.context.pushTermVar(TUnknown, def.name.text);
        const bound = this.infer(def.bound);
        // The same level, so anything that already points here still does.
        this.context.truncate(level);
        this.context.pushTermVar(bound, def.name.text);
      }

      for (const [index, def] of term.defs.entries()) {
        const signature = signatures.get(index);
        if (signature !== undefined) this.check(def.bound, signature);
      }

      return this.check(term.body, expected);
    });
    this.context.assertClosed("def group", [result]);
    return result;
  }

  // --------------------------------------------------------------- synthesis

  #inferVar(term: Extract<TermNode, { kind: "Var" }>): Type {
    const found = this.context.lookupTerm(term.name.text);
    if (found !== undefined) return found.entry.type;
    return badUnder(
      this.#report(
        `unknown name ${term.name.text}`,
        term.name.at,
        term.name.text.length,
      ),
    );
  }

  /**
   * An application checked against an expected type.
   *
   * The expected type says nothing about the arguments, but it does say
   * something about the type arguments, so it joins the argument list as one
   * more constraint on the same batch -- which is what lets `empty()` at
   * `List[Bool]` pick `Bool`.
   *
   * A constraint and not a demand: the result is still coerced towards it
   * afterwards by `check`, on the solved types, which is where a mismatch is
   * reported.
   */
  #applyCall(
    term: Extract<TermNode, { kind: "App" }>,
    expected: TypePattern,
  ): Type {
    const callee = this.subtyper.expose(this.infer(term.callee));
    if (callee.kind !== "TFun") {
      // Two heads stand aside rather than being wrong. `<bad>` because a
      // report already stands; `never` because it sits under
      // `unknown -> never` at every arity, so it is callable with whatever is
      // written and answers `never` -- no shape to read, and nothing to say
      // about the argument count either.
      const answer = callee.kind === "TBad" || callee.kind === "TNever"
        ? callee
        : badUnder(
          this.#report(
            `${typeToString(callee)} is not a function`,
            term.callee.at,
          ),
        );
      // Still walk the arguments: errors inside them are real either way.
      for (const arg of term.args) this.infer(arg);
      return answer;
    }

    // Every argument is checked before a single EVar exists, against a
    // pattern that hides the type parameters behind missing parts: an
    // undecided type argument says nothing about an argument's shape. So
    // nothing here can reach an EVar, and batches cannot nest -- a nested call
    // opens and closes its own entirely within this loop.
    const missing = callee.typeParams.map(() => TMissing);
    const patterns = callee.params.map((param) =>
      openMany<unknown>(param, missing)
    );
    const actuals = term.args.map((arg, i) =>
      this.check(arg, patterns[i] ?? TMissing)
    );

    // An argument list of the wrong length settles the call on its own: the
    // missing arguments were what the type parameters were to be read from, so
    // there is nothing left to ask and nothing to suppress afterwards.
    if (term.args.length !== callee.params.length) {
      return badUnder(
        this.#report(
          `expected ${callee.params.length} argument${
            callee.params.length === 1 ? "" : "s"
          }, found ${term.args.length}`,
          term.at,
        ),
      );
    }

    const demanded = this.subtyper.widestMatching(expected);

    // What is left is the relating, which is all the EVars are for: the
    // complete type each argument came back with against a parameter type over
    // variables -- the dependency-free relation LTI is decidable on.
    const solutions = this.subtyper.withEVars(
      callee.typeParams.map((binder) => binder.hint),
      term.at,
      (evars) => {
        // The declared bound is a constraint like any other, so it takes part
        // in the `lower <: upper` check rather than being enforced separately.
        // Asked and not recorded directly, so that `?A <: unknown` falls out
        // as vacuous instead of needing to be excluded.
        //
        // Bounds are *parallel*, so this can never mention a sibling.
        for (const [j, binder] of callee.typeParams.entries()) {
          const evar = evars[j] ?? impossible("an EVar per type parameter");
          this.subtyper.isSubtype(evar, binder.bound);
        }

        // Opened before anything is related, so every entry is fully
        // described from the start: opening the result is what records where
        // each EVar occurs.
        const result = openWith(callee.result, (j, variance) => {
          const evar = evars[j] ??
            impossible("the result binds only this binder");
          // Once per occurrence, so two placements accumulate -- which is how
          // a variable comes to occur both ways with neither occurrence
          // invariant. Reached from a type and not from the batch, so the
          // entry is looked up here.
          const entry = this.context.evarAt(evar) ??
            impossible("the batch's variables name EVar entries");
          entry.noteOccurrence(variance);
          return evar;
        });

        // Nothing is decided until the whole list is in, so the solution is a
        // join and not a race, and the order here cannot matter.
        const params = callee.params.map((param) => openMany(param, evars));
        for (const [i, actual] of actuals.entries()) {
          const param = params[i] ?? impossible("arities agree above");
          // The argument's own position, not the call's: a bound recorded
          // under this ask is this argument's doing, so anything the subtyper
          // says about it names the argument.
          //
          // A plain `no` should be unreachable -- the complete parts of the
          // parameter type were in the pattern and are already answered for,
          // and EVar positions record rather than refuse -- so what is left is
          // `exhausted`, the relation giving up before it could record.
          const arg = term.args[i] ?? impossible("one actual per argument");
          const verdict = this.subtyper.isSubtype(actual, param, arg.at);
          if (verdict !== true) {
            this.#reportVerdict(verdict, actual, param, arg.at);
          }
        }

        // The expected type, last -- though order cannot matter, every
        // constraint being joined at once. The verdict is dropped because the
        // types it would name still hold EVars; `check` coerces towards it
        // once they are solved.
        this.subtyper.isSubtype(result, demanded);
      },
    );

    // The result the batch was instantiated from, opened with what the batch
    // came to -- the same substitution the parameter types got above, and the
    // reason nothing has to carry a type out of the scope the EVars lived in.
    const result = openMany(callee.result, solutions);
    this.context.assertClosed("application", [result]);
    return result;
  }

  #inferTypeApp(term: Extract<TermNode, { kind: "TypeApp" }>): Type {
    const callee = this.subtyper.expose(this.infer(term.callee));
    const args = term.args.map((arg) => this.elaborator.elaborateType(arg));

    if (callee.kind !== "TFun") {
      // The same two that stand aside at an application, and `never` for the
      // same reason: it is under every polymorphic function type, so it takes
      // the type arguments written and stays `never`.
      if (callee.kind === "TBad" || callee.kind === "TNever") return callee;
      return badUnder(
        this.#report(
          `${typeToString(callee)} takes no type arguments`,
          term.callee.at,
        ),
      );
    }
    if (callee.typeParams.length !== args.length) {
      return badUnder(
        this.#report(
          `expected ${callee.typeParams.length} type argument${
            callee.typeParams.length === 1 ? "" : "s"
          }, found ${args.length}`,
          term.at,
        ),
      );
    }

    for (const [j, binder] of callee.typeParams.entries()) {
      // A relation and not a coercion: an explicit type argument is a choice,
      // with nothing missing to fill and nowhere to move it to, so the only
      // question is whether it is admissible.
      const arg = args[j] ?? impossible("the arity mismatch above returns");
      const verdict = this.subtyper.isSubtype(arg, binder.bound);
      if (verdict !== true) {
        this.#reportVerdict(verdict, arg, binder.bound, term.at);
      }
    }
    // The quantifier is discharged, so what is left is a plain arrow.
    return TFun(
      [],
      callee.params.map((param) => openMany(param, args)),
      openMany(callee.result, args),
    );
  }

  // ------------------------------------------------------------------- match

  /**
   * The union level: what the arms match on, which of them a value can reach,
   * whether they leave one over, and the join of the ones that can run. Every
   * reachable arm is checked against the same pattern, so no arm is privileged
   * by position.
   *
   * The join and not a coercion of it: `check` coerces afterwards, and doing
   * it in that order lets a missing part be filled by the arms rather than
   * guessed ahead of them, only the arms having a witness for it. Sound
   * because the join is above every arm and the coercion only goes further up.
   *
   * `remaining` is the whole of the analysis: what a value could still be on
   * reaching the arm being checked, seeded from the scrutinee's *type* rather
   * than from the declaration its name reaches, so a `Cons[A]` needs one arm
   * where a `List[A]` needs both. One-level patterns keep it a set of
   * constructor names, and every question a *list* of arms raises is a
   * question about that set -- an arm is unreachable when nothing it matches
   * is left in it, and the arms are exhaustive when it is empty at the end.
   * Each is about an arm against the ones before it, which is what an arm
   * cannot see and this method can.
   */
  #checkMatch(
    term: Extract<TermNode, { kind: "Match" }>,
    expected: TypePattern,
  ): Type {
    const scrutinee = this.subtyper.expose(this.infer(term.scrutinee));
    if (scrutinee.kind !== "TData") {
      return this.#checkUnmatchable(term, scrutinee, expected);
    }
    const remaining = new Set(this.declarations.casesOf(scrutinee));

    const types: Type[] = [];
    for (const arm of term.arms) {
      // Taken and removed at once: what an arm matches is exactly what is
      // left after it, and an arm with nothing left is one nothing reaches.
      // What killed it, and the two are separate questions even where the
      // report is the same: a name the arms above it cover, against a name
      // the scrutinee's type never admitted.
      let dead: string | undefined;
      let binderTypes: readonly Type[] = [];
      if (arm.pattern.kind === "PWild") {
        if (remaining.size === 0) dead = "every value is matched above";
        remaining.clear();
      } else {
        const name = arm.pattern.name.text;
        // Resolved against the *family*: what a name means is the datatype's
        // business, and whether a value of this type could have it is the
        // question below.
        const ctor = this.declarations.ctorOf(scrutinee.family, name);
        // A name that is no constructor is a mistake of its own and answers
        // nothing about coverage: it was never in the set, so it cannot have
        // been taken out, and reporting it as matched above -- which
        // `#armBinderTypes` is about to report as no constructor at all --
        // would blame the author twice for one thing.
        // Which of the two it was, asked of the type rather than of what is
        // left: a name this type never admitted is unreachable for a reason
        // the arms above it had no part in.
        if (ctor !== undefined && !remaining.delete(name)) {
          dead = this.declarations.casesOf(scrutinee).includes(name)
            ? `${name} is matched above`
            : `no ${typeToString(scrutinee)} is a ${name}`;
        }
        binderTypes = this.#armBinderTypes(arm.pattern, ctor, scrutinee);
      }
      if (dead !== undefined) {
        this.#report(`this arm is unreachable: ${dead}`, arm.pattern.at);
      }

      // Checked whether or not it can be reached: what is written in a dead
      // arm is as wrong as it would be anywhere else, the way a mistyped
      // call's arguments are still checked. Only the *type* is dropped -- a
      // value that cannot arrive here cannot be what the match answers with,
      // and joining it in would widen the answer for an arm that never runs.
      const type = this.#checkArm(arm, binderTypes, expected);
      if (dead === undefined) types.push(type);
    }

    if (remaining.size > 0) {
      this.#report(
        `match is not exhaustive: ${[...remaining].join(", ")} not covered`,
        term.at,
      );
    }
    return this.subtyper.joinMany(types, term.at);
  }

  /**
   * A `match` with no set of constructors to work with, which is why none of
   * the analysis above applies: no arm is covered by another, none of them
   * together leave a value over, and no name written resolves. Three heads
   * arrive here and each answers for the whole match, binders and result
   * alike -- `<bad>` where a report already stands, `never` where no value
   * arrives to be taken apart, and a fresh `<bad>` for a head that is simply
   * not matchable, said once about the scrutinee rather than once per name
   * that failed to be a constructor of it.
   *
   * A `Ref` is the interesting member of that third group. It is *inhabited*
   * and still has nothing to take apart, which is exactly why it is not a
   * datatype with no constructors: the analysis above would read an empty
   * constructor set as an empty type, call every arm unreachable and answer
   * `never`.
   *
   * The arms are still checked, since what is written in them is as wrong as
   * it would be anywhere else. Their types are dropped rather than joined,
   * which is the unreachable-arm rule with every arm unreachable: nothing
   * reaches a `never` scrutinee's arms at all, and past a `<bad>` there is
   * nothing a join could be trusted to say.
   */
  #checkUnmatchable(
    term: Extract<TermNode, { kind: "Match" }>,
    scrutinee: Type,
    expected: TypePattern,
  ): Type {
    const answer = scrutinee.kind === "TBad" || scrutinee.kind === "TNever"
      ? scrutinee
      : badUnder(this.#report(
        `cannot match on ${typeToString(scrutinee)}: it is not a datatype`,
        term.scrutinee.at,
      ));
    for (const arm of term.arms) {
      this.#checkArm(
        arm,
        arm.pattern.kind === "PWild" ? [] : arm.pattern.args.map(() => answer),
        expected,
      );
    }
    return answer;
  }

  /**
   * One type per binder the pattern wrote, so the arm has nothing left to
   * reconcile: a wrong field count is padded here and said here, and so is a
   * name that is no constructor of `matched`'s family -- the family, since
   * what a name means is the datatype's business and whether this type admits
   * it is the caller's.
   *
   * Settled before the arm's scope opens, which nothing objects to: a field
   * type is the constructor's own, opened at the scrutinee's type arguments,
   * and neither that nor a report reads the context.
   */
  #armBinderTypes(
    pattern: Extract<MatchArm["pattern"], { kind: "PCtor" }>,
    ctor: DataCtorInfo | undefined,
    matched: Extract<Type, { kind: "TData" }>,
  ): readonly Type[] {
    if (ctor === undefined) {
      const bad = badUnder(this.#report(
        `${pattern.name.text} is not a constructor of ${matched.family}`,
        pattern.name.at,
        pattern.name.text.length,
      ));
      return pattern.args.map(() => bad);
    }

    // Fields are stored closed over the datatype's parameters, so the
    // scrutinee's own type arguments are what open them.
    const fields = ctorFieldsAt(ctor, matched.args);
    const spare = fields.length === pattern.args.length ? undefined : badUnder(
      this.#report(
        `${ctor.name} takes ${fields.length} field${
          fields.length === 1 ? "" : "s"
        }, bound ${pattern.args.length}`,
        pattern.at,
        ctor.name.length,
      ),
    );
    return pattern.args.map((_, j) =>
      fields[j] ?? spare ?? impossible("a binder past a matching arity")
    );
  }

  /**
   * One arm: its binders, and its body under them.
   *
   * The binders go into a scope of their own, so the type coming out may not
   * mention them, which `assertClosed` says out loud. Nothing about the
   * datatype reaches here -- what each binder is was settled by the caller,
   * which is the only place that knows what the whole match is over.
   */
  #checkArm(
    arm: MatchArm,
    binderTypes: readonly Type[],
    expected: TypePattern,
  ): Type {
    const binders = arm.pattern.kind === "PWild" ? [] : arm.pattern.args;
    const type = this.context.inScope(() => {
      this.#reportDuplicateBinders(binders, "pattern");
      for (const [j, binder] of binders.entries()) {
        this.context.pushTermVar(
          binderTypes[j] ?? impossible("one type per written binder"),
          binder.text,
        );
      }
      return this.check(arm.body, expected);
    });
    this.context.assertClosed("match arm", [type]);
    return type;
  }
}

/** Check a whole program, handing back its type and every diagnostic. */
export function checkProgram(
  program: Program,
): { type: Type; diagnostics: readonly Diagnostic[] } {
  const checker = new Checker();
  const type = checker.checkProgram(program);
  return { type, diagnostics: checker.diagnostics };
}
