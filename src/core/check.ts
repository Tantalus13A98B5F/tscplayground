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
} from "../syntax/ast.ts";
import { Context } from "./context.ts";
import { type CtorInfo, Declarations } from "./declarations.ts";
import { ctorFieldsAt, Elaborator } from "./elaborate.ts";
import { Subtyper, type Verdict } from "./subtype.ts";
import {
  closeFrom,
  EVar,
  FVar,
  type Level,
  openMany,
  polarityOf,
  TBad,
  TFun,
  TNever,
  type Type,
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
    return this.context.apply(this.infer(program.term));
  }

  #report(message: string, at: Position, width = 1): void {
    this.diagnostics.push(reportError(message, at, width));
  }

  /** Report a verdict other than `yes`, each in its own words. */
  #reportVerdict(
    verdict: Verdict,
    actual: Type,
    expected: Type,
    at: Position,
  ): void {
    const found = typeToString(this.context.apply(actual));
    const wanted = typeToString(this.context.apply(expected));
    switch (verdict) {
      case "yes":
        return;
      case "no":
        return this.#report(`expected ${wanted}, found ${found}`, at);
      case "exhausted":
        // The checker's limit, not the program's mistake. Saying "found X,
        // expected Y" here would send someone looking for a bug that is not
        // in their code.
        return this.#report(
          `gave up comparing ${found} with ${wanted}: too deeply nested`,
          at,
        );
      case "interdependent":
        // Any sibling, not only one further right: they are decided together
        // and each on its own occurrences, so one leaning on another is a
        // dependency the solver has no order to resolve.
        return this.#report(
          `cannot infer a type argument from ${found}: it depends on another ` +
            `type argument of the same call, so give it explicitly`,
          at,
        );
    }
  }

  /** `actual <: expected`, reporting if not. */
  #subsume(actual: Type, expected: Type, at: Position): void {
    const verdict = this.subtyper.isSubtype(actual, expected);
    if (verdict !== "yes") this.#reportVerdict(verdict, actual, expected, at);
  }

  // ---------------------------------------------------------------- checking

  check(term: TermNode, expected: Type): Type {
    switch (term.kind) {
      // The forms with a checking rule of their own: each pushes the expected
      // type *inward* rather than inferring and comparing at the end, which is
      // the only way an unannotated parameter ever gets a type.
      case "Abs":
        return this.#checkAbs(term, expected);
      case "Match":
        return this.#checkMatch(term, expected);
      case "Let":
        return this.#checkLet(term, expected);
      default: {
        this.#subsume(this.infer(term), expected, term.at);
        return expected;
      }
    }
  }

  #checkAbs(
    term: Extract<TermNode, { kind: "Abs" }>,
    expected: Type,
  ): Type {
    const wanted = this.subtyper.expose(expected);
    if (
      wanted.kind !== "TFun" ||
      wanted.typeParams.length !== term.typeParams.length ||
      wanted.params.length !== term.params.length
    ) {
      // Not a function of this shape, so there is nothing to push inward.
      // Inferring instead reports the mismatch *and* any error in the body.
      this.#subsume(this.infer(term), expected, term.at);
      return expected;
    }

    this.context.inScope(() => {
      // The expected type's bounds are what the body may assume.
      const opened = wanted.typeParams.map((binder, j) => {
        const declared = term.typeParams[j];
        const name = declared === undefined
          ? binder.hint
          : bindingHint(declared.name);
        // Only a written name can clash; a hint borrowed from the expected
        // type is not a binding anyone wrote.
        if (declared !== undefined) {
          this.elaborator.reportDeclaredName(declared.name);
        }
        if (declared?.bound !== undefined) {
          // Contravariant: a lambda may promise less of its type parameter
          // than the expected type does, never more.
          const written = this.elaborator.elaborateType(declared.bound);
          this.#subsume(binder.bound, written, declared.at);
        }
        return FVar(this.context.pushTypeVar(binder.bound, name), name);
      });

      const params = wanted.params.map((param) => openMany(param, opened));
      const result = openMany(wanted.result, opened);

      this.#reportDuplicateBinders(
        term.params.map((param) => param.name),
        "parameter list",
      );
      for (const [j, param] of term.params.entries()) {
        this.#bindParam(param, params[j] ?? TBad);
      }
      this.check(term.body, result);
    });
    return expected;
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

  /** Bind one parameter, preferring its annotation where it has one. */
  #bindParam(param: Param, fromContext: Type): void {
    let type = fromContext;
    if (param.annotation !== undefined) {
      const written = this.elaborator.elaborateType(param.annotation);
      // The annotation must accept everything the caller may pass.
      this.#subsume(fromContext, written, param.at);
      type = written;
    }
    this.#pushBinding(param.name, type);
  }

  #checkLet(term: Extract<TermNode, { kind: "Let" }>, expected: Type): Type {
    this.context.inScope(() => {
      this.#pushBinding(term.name, this.#letBinding(term));
      this.check(term.body, expected);
    });
    return expected;
  }

  // --------------------------------------------------------------- inference

  infer(term: TermNode): Type {
    switch (term.kind) {
      case "Var":
        return this.#inferVar(term);
      case "Abs":
        return this.#inferAbs(term);
      case "App":
        return this.#inferApp(term);
      case "TypeApp":
        return this.#inferTypeApp(term);
      case "Let":
        return this.#inferLet(term);
      case "Match":
        return this.#inferMatch(term);
    }
  }

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

  #inferAbs(term: Extract<TermNode, { kind: "Abs" }>): Type {
    const type = this.context.inScope((mark) => {
      const binders = this.elaborator.bindTypeParams(term.typeParams);

      const params = term.params.map((param) => {
        if (param.annotation !== undefined) {
          return this.elaborator.elaborateType(param.annotation);
        }
        // Inference has nothing to draw on -- and never invents an EVar for it,
        // since a parameter's type is not something local inference guesses.
        this.#report(
          `cannot infer a type for ${bindingHint(param.name)}: annotate it, ` +
            `or use this function where its parameter types are known`,
          param.name.at,
          bindingHint(param.name).length,
        );
        return TBad;
      });
      this.#reportDuplicateBinders(
        term.params.map((param) => param.name),
        "parameter list",
      );
      for (const [j, param] of term.params.entries()) {
        this.#pushBinding(param.name, params[j] ?? TBad);
      }

      // Applied before closing: an EVar solved inside the body must be gone
      // before the entry holding its solution is truncated away.
      const result = this.context.apply(this.infer(term.body));

      return TFun(
        binders,
        params.map((param) => closeFrom(param, mark)),
        closeFrom(result, mark),
      );
    });
    this.context.assertClosed("function", [type]);
    return type;
  }

  #inferApp(term: Extract<TermNode, { kind: "App" }>): Type {
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

    const result = this.context.inScope(() => {
      // One EVar per type parameter. This is the only place they are created,
      // and one batch, which is the unit `#solveEVars` decides at once.
      const levels = this.context.pushEVarBatch(
        callee.typeParams.map((binder) => binder.hint),
      );
      const evars: Type[] = [];
      for (const [j, binder] of callee.typeParams.entries()) {
        const level = levels[j];
        if (level === undefined) continue;
        evars.push(EVar(level, binder.hint));
        // The declared bound is an upper bound like any other, so it takes part
        // in the `lower <: upper` check rather than being enforced separately.
        //
        // Bounds are *parallel*: one may name an enclosing binder but never a
        // member of its own group, so this can never mention a sibling EVar --
        // which `addConstraint` would refuse.
        if (binder.bound.kind !== "TUnknown") {
          this.context.addConstraint(level, "upper", binder.bound);
        }
      }

      const params = callee.params.map((param) => openMany(param, evars));
      if (term.args.length !== params.length) {
        this.#report(
          `expected ${params.length} argument${
            params.length === 1 ? "" : "s"
          }, found ${term.args.length}`,
          term.at,
        );
      }

      // Left to right, each contributing constraints; nothing is decided until
      // the whole list is in, so the solution is a join and not a race.
      for (const [i, arg] of term.args.entries()) {
        const param = params[i];
        if (param === undefined) this.infer(arg);
        else this.check(arg, param);
      }

      // Built before solving, not after: which bound an EVar takes depends on
      // how it occurs *here*, so this is an input to the solver and not only
      // its output.
      const result = openMany(callee.result, evars);
      this.#solveEVars(levels, result, term.at);
      return this.context.apply(result);
    });
    this.context.assertClosed("application", [result]);
    return result;
  }

  /**
   * Decide every EVar of one argument list at once, ascending so a later
   * solution may mention an earlier one.
   *
   * The levels are passed rather than scanned for. `#inferApp` created them and
   * knows exactly which they are, so looking for them again would be asking the
   * context a question the caller had already answered -- and would have to
   * treat "not an EVar" as an ordinary answer, which by then it never is.
   *
   * `result` is the type the application hands back, and the selection between
   * an EVar's two bounds is read off how it occurs in it. Members of one batch
   * never depend on each other -- `#constrain` refuses that -- so each is
   * decided on its own occurrences alone, with no ordering among them to get
   * right.
   *
   * Every failure solves to `TBad`. Checking against a bad type always
   * succeeds, so one uninferable argument does not go on to fail again wherever
   * the result is used.
   */
  #solveEVars(levels: readonly Level[], result: Type, at: Position): void {
    for (const level of levels) {
      const entry = this.context.evarAt(level);
      if (entry.solution !== undefined) continue;

      // A refused constraint was reported where it was refused, so this one is
      // bad already and silently: whatever bounds did get through describe a
      // variable the checker has given up on, and solving from them could only
      // report the same mistake a second time under a different name.
      if (entry.refused) {
        this.context.setSolution(level, TBad);
        continue;
      }

      const solved = this.subtyper.solveEVar(
        level,
        polarityOf(level, result),
      );
      switch (solved.kind) {
        case "solved":
          this.context.setSolution(level, this.context.apply(solved.type));
          break;
        case "unconstrained":
          // Bottom would do, and would even be principal. It is refused all the
          // same: `never` propagates outward as a type the author never wrote
          // and cannot act on, and the mistake it usually stands for -- an
          // argument list that says nothing about a type parameter -- is better
          // named where it happened.
          this.#report(
            `cannot infer the type argument ${entry.hint}: ` +
              `nothing constrains it, so give it explicitly`,
            at,
          );
          this.context.setSolution(level, TBad);
          break;
        case "conflict":
          this.#reportVerdict(solved.verdict, solved.lower, solved.upper, at);
          this.context.setSolution(level, TBad);
          break;
      }
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
      this.#subsume(args[j] ?? TBad, binder.bound, term.at);
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
    return this.context.apply(this.infer(term.bound));
  }

  #inferLet(term: Extract<TermNode, { kind: "Let" }>): Type {
    const result = this.context.inScope(() => {
      this.#pushBinding(term.name, this.#letBinding(term));
      return this.context.apply(this.infer(term.body));
    });
    // With no dependent types a term variable cannot appear in a type, so a
    // `let` body's type never mentions the binding -- but say so out loud.
    this.context.assertClosed("let", [result]);
    return result;
  }

  // ------------------------------------------------------------------- match

  #inferMatch(term: Extract<TermNode, { kind: "Match" }>): Type {
    const scrutinee = this.subtyper.expose(this.infer(term.scrutinee));
    // Every arm is inferred on its own and the results joined, so no arm is
    // privileged by position. With no arms at all the join is `never`, which
    // is right: a match on an uninhabited scrutinee returns nothing.
    return this.#armTypes(term, scrutinee, undefined)
      .reduce((left, right) => this.subtyper.join(left, right), TNever);
  }

  #checkMatch(
    term: Extract<TermNode, { kind: "Match" }>,
    expected: Type,
  ): Type {
    const scrutinee = this.subtyper.expose(this.infer(term.scrutinee));
    this.#armTypes(term, scrutinee, expected);
    return expected;
  }

  /**
   * Check every arm -- against `expected` if there is one, otherwise inferring
   * each for the caller to join. Also settles exhaustiveness, which one-level
   * patterns make a set difference rather than a decision procedure.
   */
  #armTypes(
    term: Extract<TermNode, { kind: "Match" }>,
    scrutinee: Type,
    expected: Type | undefined,
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
    expected: Type | undefined,
  ): Type {
    const type = this.context.inScope(() => {
      if (arm.pattern.kind === "PCtor") {
        this.#bindPattern(arm.pattern, owner, args);
      }
      return expected === undefined
        ? this.context.apply(this.infer(arm.body))
        : (this.check(arm.body, expected), expected);
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
    // The scrutinee's own datatype is the only place to look: it names the
    // constructors that can possibly appear, so no reverse map is needed.
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
