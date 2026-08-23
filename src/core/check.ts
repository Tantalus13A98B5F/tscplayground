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
  type Param,
  type Program,
  type TermNode,
  type TypeParam,
} from "../syntax/ast.ts";
import { Context } from "./context.ts";
import { type CtorInfo, Declarations } from "./declarations.ts";
import { ctorFieldsAt, Elaborator } from "./elaborate.ts";
import {
  castComplete,
  Subtyper,
  type TypeArgFailure,
  type Verdict,
} from "./subtype.ts";
import {
  closeFrom,
  FVar,
  impossible,
  mkLevel,
  openMany,
  openWith,
  TBad,
  TFun,
  TMissing,
  TNever,
  TUnknown,
  type Type,
  type TypePattern,
  typeToString,
} from "./types.ts";

export class Checker {
  readonly declarations = new Declarations();
  readonly context = new Context();
  readonly diagnostics: Diagnostic[] = [];
  readonly elaborator: Elaborator;
  readonly subtyper: Subtyper;

  constructor() {
    this.elaborator = new Elaborator(
      this.declarations,
      this.context,
      this.diagnostics,
    );
    this.subtyper = new Subtyper(this.context);
  }

  /** Declarations first, then constructors, then the one term they serve. */
  checkProgram(program: Program): Type {
    this.elaborator.elaborateDeclarations(program.decls);
    this.elaborator.seedConstructors();
    return this.infer(program.term);
  }

  #report(message: string, at: Position, width = 1): void {
    this.diagnostics.push(reportError(message, at, width));
  }

  /** Report a verdict other than `yes`, each in its own words. */
  #reportVerdict(
    verdict: Verdict,
    actual: Type,
    expected: TypePattern,
    at: Position,
  ): void {
    const found = typeToString(actual);
    const wanted = typeToString(expected);
    switch (verdict) {
      case "yes":
        return;
      case "no":
        return this.#report(`expected ${wanted}, found ${found}`, at);
      case "exhausted":
        // The checker's limit, not the program's mistake, so not "found X,
        // expected Y".
        return this.#report(
          `gave up comparing ${found} with ${wanted}: too deeply nested`,
          at,
        );
      case "interdependent":
        // Any sibling, not only one further right: they are decided together
        // and each on its own occurrences, so one leaning on another is a
        // dependency no order resolves.
        return this.#report(
          `cannot infer a type argument from ${found}: it depends on another ` +
            `type argument of the same call, so give it explicitly`,
          at,
        );
    }
  }

  /**
   * What a term of type `actual` is, seen at `expected`: the least supertype
   * of the one matching the other, reported once if there is none.
   *
   * What a checking rule returns, in place of subsuming and then handing back
   * the expected type. On a type written in full the two agree -- a complete
   * pattern matches only itself -- and where the pattern is partial the answer
   * is its shape with the term's own content in the missing parts.
   *
   * Nearly the only way a type meets an expected one. What is left beside it
   * is a written type argument against its declared bound, a relation rather
   * than a coercion, which asks `isSubtype` directly.
   */
  #coerce(actual: Type, expected: TypePattern, at: Position): Type {
    const cast = this.subtyper.upcast(actual, expected);
    if (cast.verdict !== "yes") {
      this.#reportVerdict(cast.verdict, actual, expected, at);
    }
    return cast.type;
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
   * what `#coerce` produces.
   */
  check(term: TermNode, expected: TypePattern): Type {
    switch (term.kind) {
      // The forms with a rule of their own: each pushes the pattern *inward*
      // rather than synthesizing and comparing at the end, which is the only
      // way an unannotated parameter ever gets a type.
      case "Abs":
        return this.#checkAbs(term, expected);
      case "Match":
        return this.#checkMatch(term, expected);
      case "Let":
        return this.#checkLet(term, expected);
      case "App":
        return this.#checkApp(term, expected);
      // The two forms with nothing to push inward: a name already has a type
      // and a type application already says what it is. They synthesize, and
      // the pattern is applied afterwards.
      case "Var":
        return this.#coerce(this.#inferVar(term), expected, term.at);
      case "TypeApp":
        return this.#coerce(this.#inferTypeApp(term), expected, term.at);
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
   * otherwise, and the coercion at the end makes the answer the type asked
   * for. Nothing in between relates anything: a disagreement with the pattern
   * is the lambda having the wrong type, and that is said once.
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
        term.typeParams.map((declared, j) =>
          this.#boundType(
            declared,
            // Top where there is no pattern, which is what an unbounded type
            // parameter means anyway. This is the one place the two rules
            // differ, and it is the whole of the difference: a bound left
            // unsaid has a sound reading and a parameter type does not.
            wanted?.typeParams[j]?.bound ?? TUnknown,
          )
        ),
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
      // arity -- the count is a disagreement the coercion says.
      const params = term.params.map((param, j) =>
        this.#paramType(
          param,
          // A parameter the pattern does not reach is one it says nothing
          // about, which is what a missing part means -- so it is asked for
          // like any other rather than standing `<bad>`, which would claim
          // something was supplied.
          wanted === undefined
            ? TMissing
            : openMany(wanted.params[j] ?? TMissing, opened),
        )
      );
      for (const [j, param] of term.params.entries()) {
        this.#pushBinding(
          param.name,
          params[j] ?? impossible("one type per written parameter"),
        );
      }

      const result = this.check(
        term.body,
        openMany(wanted?.result ?? TMissing, opened),
      );

      // Closing the parts at the mark is what turns level `mark + j` back
      // into `BVar j`.
      return TFun(
        binders,
        params.map((param) => closeFrom(param, mark)),
        closeFrom(result, mark),
      );
    });
    this.context.assertClosed("function", [type]);
    return this.#coerce(type, expected, term.at);
  }

  /**
   * One type parameter's bound: what is written if anything is, else what the
   * pattern supplies if that is complete, else `<bad>` and the error.
   *
   * A missing bound could quietly become `unknown` instead, assuming less of a
   * type variable being safe. More precise and worse: two positions that read
   * the same in the source would answer differently for a reason an author
   * cannot see.
   */
  #boundType(declared: TypeParam, supplied: TypePattern): Type {
    if (declared.bound !== undefined) {
      return this.elaborator.elaborateType(declared.bound);
    }
    const filled = castComplete(supplied);
    if (filled.verdict !== "yes") {
      const name = bindingHint(declared.name);
      this.#report(
        `cannot infer a bound for ${name}: write it, or use this function ` +
          `where its bounds are known`,
        declared.name.at,
        name.length,
      );
    }
    return filled.type;
  }

  /**
   * One parameter's type, by the same rule as `#boundType`, spelled out twice
   * rather than shared because the two differ only in their words.
   *
   * What is written wins whole and unconditionally, including where it
   * disagrees with the pattern: the body is typed against what the author
   * wrote, and the disagreement is the lambda's type not being the one asked
   * for, which the coercion at `#checkAbs` says once and in full. Relating the
   * two here would buy a message at the parameter and pay for it by discarding
   * the annotation -- the one thing this rule promises to keep.
   */
  #paramType(param: Param, supplied: TypePattern): Type {
    if (param.annotation !== undefined) {
      return this.elaborator.elaborateType(param.annotation);
    }
    const filled = castComplete(supplied);
    if (filled.verdict !== "yes") {
      const name = bindingHint(param.name);
      this.#report(
        `cannot infer a type for ${name}: annotate it, or use this function ` +
          `where its parameter types are known`,
        param.name.at,
        name.length,
      );
    }
    return filled.type;
  }

  /**
   * Bind a source binder: a parameter, a `let`, a pattern field. A wildcard
   * binds its position and no name, so nothing ever resolves to it.
   */
  #pushBinding(binder: BindingIdent, type: Type): void {
    this.context.pushTermVar(type, binder.text);
  }

  /** Report a name bound twice in one group: a parameter list, a pattern. */
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
      this.#pushBinding(term.name, this.#letBinding(term));
      return this.check(term.body, expected);
    });
    // With no dependent types a `let` body's type cannot mention the binding,
    // but say so out loud.
    this.context.assertClosed("let", [result]);
    return result;
  }

  // --------------------------------------------------------------- synthesis

  #inferVar(term: Extract<TermNode, { kind: "Var" }>): Type {
    const found = this.context.lookupTerm(term.name.text);
    if (found !== undefined) return found.entry.type;
    this.#report(
      `unknown name ${term.name.text}`,
      term.name.at,
      term.name.text.length,
    );
    return TBad;
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
   * afterwards, on the solved types, which is where a mismatch is reported.
   */
  #checkApp(
    term: Extract<TermNode, { kind: "App" }>,
    expected: TypePattern,
  ): Type {
    return this.#coerce(this.#applyCall(term, expected), expected, term.at);
  }

  #applyCall(
    term: Extract<TermNode, { kind: "App" }>,
    expected: TypePattern,
  ): Type {
    const callee = this.subtyper.expose(this.infer(term.callee));
    if (callee.kind !== "TFun") {
      if (callee.kind !== "TBad") {
        this.#report(
          `${typeToString(callee)} is not a function`,
          term.callee.at,
        );
      }
      // Still walk the arguments: errors inside them are real either way.
      for (const arg of term.args) this.infer(arg);
      return TBad;
    }

    // Every argument is checked before a single EVar exists, against a
    // pattern that hides the type parameters behind missing parts: an
    // undecided type argument says nothing about an argument's shape. So
    // nothing here can reach an EVar, and batches cannot nest -- a nested call
    // opens and closes its own entirely within this loop.
    const missing = callee.typeParams.map(() => TMissing);
    const patterns = callee.params.map((param) =>
      openMany<number>(param, missing)
    );
    const actuals = term.args.map((arg, i) =>
      this.check(arg, patterns[i] ?? TMissing)
    );

    // An argument list of the wrong length settles the call on its own: the
    // missing arguments were what the type parameters were to be read from, so
    // there is nothing left to ask and nothing to suppress afterwards.
    if (term.args.length !== callee.params.length) {
      this.#report(
        `expected ${callee.params.length} argument${
          callee.params.length === 1 ? "" : "s"
        }, found ${term.args.length}`,
        term.at,
      );
      return TBad;
    }

    // The widest type the expected pattern admits, which is what a pattern
    // says as an upper bound: a missing part becomes the extreme for its
    // polarity, so only the written parts constrain. A complete pattern gives
    // itself back, and `TMissing` gives `unknown`.
    const demanded = this.subtyper.downcast(TUnknown, expected).type;

    // What is left is the relating, which is all the EVars are for: the
    // complete type each argument came back with against a parameter type over
    // variables -- the dependency-free relation LTI is decidable on.
    const { result, failures } = this.subtyper.withEVars(
      callee.typeParams.map((binder) => binder.hint),
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
        // described from the start: opening the result is what records each
        // EVar's polarity.
        const result = openWith(callee.result, (j, polarity) => {
          const evar = evars[j] ??
            impossible("the result binds only this binder");
          // Once per occurrence, so two placements combine -- which is where
          // `invariant` comes from when neither occurrence is.
          this.context.notePolarity(evar.level, polarity);
          return evar;
        });

        // Nothing is decided until the whole list is in, so the solution is a
        // join and not a race, and the order here cannot matter.
        const params = callee.params.map((param) => openMany(param, evars));
        for (const [i, actual] of actuals.entries()) {
          const param = params[i] ?? impossible("arities agree above");
          // Reported here and not left to the solver. A plain `no` should be
          // unreachable: the complete parts of the parameter type were in the
          // pattern and are already answered for, and EVar positions record
          // rather than refuse. `interdependent` and `exhausted` are the
          // relation declining to record, which nothing downstream notices --
          // an EVar it gave up on is marked as already reported.
          const verdict = this.subtyper.isSubtype(actual, param);
          if (verdict !== "yes") {
            const arg = term.args[i] ?? impossible("one actual per argument");
            this.#reportVerdict(verdict, actual, param, arg.at);
          }
        }

        // The expected type, last -- though order cannot matter, every
        // constraint being joined at once. The verdict is dropped because the
        // types it would name still hold EVars; `#checkApp` asks again once
        // they are solved.
        this.subtyper.isSubtype(result, demanded);
        return result;
      },
    );

    for (const failure of failures) this.#reportTypeArg(failure, term.at);
    this.context.assertClosed("application", [result]);
    return result;
  }

  /**
   * Say that a type argument could not be settled. Three reasons, each its own
   * message: `Subtyper` decides, and has no diagnostics to say it with.
   */
  #reportTypeArg(failure: TypeArgFailure, at: Position): void {
    switch (failure.reason.kind) {
      case "unconstrained":
        // Bottom would do, and would even be principal, but it propagates
        // outward as a type the author never wrote and cannot act on. The
        // mistake it stands for is better named where it happened.
        this.#report(
          `cannot infer the type argument ${failure.hint}: ` +
            `nothing constrains it, so give it explicitly`,
          at,
        );
        return;
      case "conflict":
        this.#reportVerdict(
          failure.reason.verdict,
          failure.reason.lower,
          failure.reason.upper,
          at,
        );
        return;
      case "disagrees":
        // Not "expected X, found Y": both bounds hold, and either would check.
        // What is missing is a reason to prefer one, which only the author has.
        this.#report(
          `cannot infer the type argument ${failure.hint}: it occurs ` +
            `invariantly, and the arguments bound it only between ` +
            `${typeToString(failure.reason.lower)} and ` +
            `${typeToString(failure.reason.upper)}, so no choice is the ` +
            `general one; give it explicitly`,
          at,
        );
        return;
    }
  }

  #inferTypeApp(term: Extract<TermNode, { kind: "TypeApp" }>): Type {
    const callee = this.subtyper.expose(this.infer(term.callee));
    const args = term.args.map((arg) => this.elaborator.elaborateType(arg));

    if (callee.kind !== "TFun") {
      if (callee.kind !== "TBad") {
        this.#report(
          `${typeToString(callee)} takes no type arguments`,
          term.callee.at,
        );
      }
      return TBad;
    }
    if (callee.typeParams.length !== args.length) {
      this.#report(
        `expected ${callee.typeParams.length} type argument${
          callee.typeParams.length === 1 ? "" : "s"
        }, found ${args.length}`,
        term.at,
      );
      return TBad;
    }

    for (const [j, binder] of callee.typeParams.entries()) {
      // A relation and not a coercion: an explicit type argument is a choice,
      // with nothing missing to fill and nowhere to move it to, so the only
      // question is whether it is admissible.
      const arg = args[j] ?? impossible("the arity mismatch above returns");
      const verdict = this.subtyper.isSubtype(arg, binder.bound);
      if (verdict !== "yes") {
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

  /** The type a `let` binds, whether ascribed or synthesized. */
  #letBinding(
    term: Extract<TermNode, { kind: "Let" } | { kind: "LetItem" }> | {
      annotation?: Parameters<Elaborator["elaborateType"]>[0];
      bound: TermNode;
    },
  ): Type {
    if (term.annotation !== undefined) {
      const ascribed = this.elaborator.elaborateType(term.annotation);
      this.check(term.bound, ascribed);
      return ascribed;
    }
    return this.infer(term.bound);
  }

  // ------------------------------------------------------------------- match

  /**
   * Every arm is checked against the same pattern and the results joined, so
   * no arm is privileged by position. With no arms at all the join is `never`,
   * which is right: a match on an uninhabited scrutinee returns nothing.
   *
   * Joining and *then* coercing lets a missing part be filled by the arms
   * rather than guessed ahead of them, only the arms having a witness for it.
   * Sound because the join is above every arm and the coercion only goes
   * further up.
   */
  #checkMatch(
    term: Extract<TermNode, { kind: "Match" }>,
    expected: TypePattern,
  ): Type {
    const scrutinee = this.subtyper.expose(this.infer(term.scrutinee));
    const joined = this.#armTypes(term, scrutinee, expected)
      .reduce((left, right) => this.subtyper.join(left, right), TNever);
    return this.#coerce(joined, expected, term.at);
  }

  /**
   * Check every arm against the pattern, for the caller to join. Also settles
   * exhaustiveness, which one-level patterns make a set difference rather than
   * a decision procedure.
   */
  #armTypes(
    term: Extract<TermNode, { kind: "Match" }>,
    scrutinee: Type,
    expected: TypePattern,
  ): Type[] {
    const datatype = scrutinee.kind === "TData"
      ? this.declarations.datatypeOf(scrutinee.name)
      : undefined;
    if (scrutinee.kind !== "TData" && scrutinee.kind !== "TBad") {
      this.#report(
        `cannot match on ${typeToString(scrutinee)}: it is not a datatype`,
        term.scrutinee.at,
      );
    }

    const args = scrutinee.kind === "TData" ? scrutinee.args : [];
    const covered = new Set<string>();
    let wild = false;
    const types: Type[] = [];

    for (const arm of term.arms) {
      if (arm.pattern.kind === "PWild") wild = true;
      else {
        const name = arm.pattern.name.text;
        if (covered.has(name)) {
          this.#report(
            `constructor ${name} is matched twice`,
            arm.pattern.at,
            name.length,
          );
        }
        covered.add(name);
      }
      types.push(this.#checkArm(arm, datatype?.name, args, expected));
    }

    if (!wild && datatype !== undefined) {
      const missing = datatype.ctors
        .map((ctor) => ctor.name)
        .filter((name) => !covered.has(name));
      if (missing.length > 0) {
        this.#report(
          `match is not exhaustive: ${missing.join(", ")} not covered`,
          term.at,
        );
      }
    }
    return types;
  }

  #checkArm(
    arm: MatchArm,
    owner: string | undefined,
    args: readonly Type[],
    expected: TypePattern,
  ): Type {
    const type = this.context.inScope(() => {
      if (arm.pattern.kind === "PCtor") {
        this.#bindPattern(arm.pattern, owner, args);
      }
      return this.check(arm.body, expected);
    });
    this.context.assertClosed("match arm", [type]);
    return type;
  }

  #bindPattern(
    pattern: Extract<MatchArm["pattern"], { kind: "PCtor" }>,
    owner: string | undefined,
    args: readonly Type[],
  ): void {
    const name = pattern.name.text;
    // The scrutinee's own datatype names every constructor that can appear,
    // so no reverse map is needed.
    const ctor = owner === undefined
      ? undefined
      : this.declarations.ctorOf(owner, name);

    if (ctor === undefined) {
      if (owner !== undefined) {
        this.#report(
          `${name} is not a constructor of ${owner}`,
          pattern.name.at,
          name.length,
        );
      }
      for (const binder of pattern.args) this.#pushBinding(binder, TBad);
      return;
    }

    this.#bindFields(pattern, ctor, args);
  }

  #bindFields(
    pattern: Extract<MatchArm["pattern"], { kind: "PCtor" }>,
    ctor: CtorInfo,
    args: readonly Type[],
  ): void {
    // Fields are stored closed over the datatype's parameters, so the
    // scrutinee's own type arguments are what open them.
    const fields = ctorFieldsAt(ctor, args);
    if (fields.length !== pattern.args.length) {
      this.#report(
        `${ctor.name} takes ${fields.length} field${
          fields.length === 1 ? "" : "s"
        }, bound ${pattern.args.length}`,
        pattern.at,
        ctor.name.length,
      );
    }
    this.#reportDuplicateBinders(pattern.args, "pattern");
    for (const [j, binder] of pattern.args.entries()) {
      // `TBad` where the pattern binds more than the constructor has: the
      // mismatch is reported above, and this keeps the arm's body checkable.
      this.#pushBinding(binder, fields[j] ?? TBad);
    }
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
