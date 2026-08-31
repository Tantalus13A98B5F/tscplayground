/**
 * Evaluation: closures, constructed values, and cells, over the surface tree.
 *
 * Untyped, and deliberately so. It imports nothing from `types.ts`, runs on any
 * program that *parsed*, and is never told whether one checked -- which is what
 * lets an ill-typed program be run on purpose, the only way to see what the
 * checker was buying. Types are skipped rather than handled: a parameter's
 * annotation, a `TypeApp`'s arguments and a `MissingParamType` alike are never
 * read, so an unwritten or unknown type is no error here and needs no case.
 *
 * Scope is the exception, and is not a type question. Where a name resolves is
 * something the checker and this must agree on or the two disagree about what a
 * program *means*, so `#tie` follows `#checkLetRec` phase for phase -- see
 * there. Reading `def.annotation` for its *presence* is reading the tree, not
 * the type.
 *
 * Every other shape a checked program would have guaranteed is tested, and the
 * vocabulary that comes of it is one rule seen from several sides: a value
 * arrived where a different shape was needed.
 *
 * One diagnostic, at the first stuck term, and then nothing. Checking recovers
 * because it is structural recursion -- every subterm is visited whatever its
 * siblings did, so absorbing a failure buys the reports from the rest of the
 * tree. This walks a *trace*, where past the first stuck term there is no rest
 * that was going to be visited anyway: what could still be reported is either a
 * consequence of the first failure or an artifact of the order arguments happen
 * to be evaluated in, and the second is not something a test should pin. There
 * is no bad value for the same reason `TBad` is a good type -- it exists so
 * that checking can go on, and nothing goes on from here.
 */

import {
  type Diagnostic,
  failed,
  type Position,
  produced,
  reportError,
  type Result,
} from "../diagnostics/diagnostic.ts";
import type {
  BindingIdent,
  DefItem,
  Ident,
  MatchPat,
  Param,
  Program,
  TermNode,
  TypeDecl,
} from "../syntax/ast.ts";

/**
 * What a constructor is, apart from its fields: the datatype it builds, and
 * whether the declaration wrote a parameter list. `| True` is a value and
 * `| True()` a function of no arguments, exactly as `CtorDecl` has it.
 */
type CtorShape = {
  readonly name: string;
  readonly datatype: string;
  readonly arity: number;
  readonly isValue: boolean;
};

/** Where a cell lives. An index into the run's `Heap`, and nothing else. */
export type Addr = number & { readonly __brand: "Addr" };

export type Value =
  /** A `fn` and the scope it was written in. */
  | {
    readonly kind: "VFun";
    readonly params: readonly Param[];
    readonly body: TermNode;
    readonly scope: Scope;
  }
  /** A saturated constructor. Its shape says what it is a value of. */
  | {
    readonly kind: "VData";
    readonly ctor: CtorShape;
    readonly fields: readonly Value[];
  }
  /** A cell, as its address. What is at that address is the heap's business. */
  | { readonly kind: "VRef"; readonly addr: Addr }
  /**
   * A function this file supplies rather than the program: `ref!` and its two
   * companions, and every constructor that takes fields. Both are functions of
   * a fixed arity and nothing else, so they need no separate value kind.
   */
  | {
    readonly kind: "VPrim";
    readonly name: string;
    readonly arity: number;
    readonly apply: (args: readonly Value[], at: Position) => Value;
  };

/**
 * Every cell a run has allocated, addressed rather than held.
 *
 * A `VRef` carries an index and never the cell itself, so allocation is a step
 * this file takes rather than one the host takes behind it. That is the whole
 * point: a budget on cells, a count of them, or anything that walks them needs
 * somewhere to be, and there is nowhere if the host heap is the heap. Dense and
 * extended only by `alloc`, so every address a value can hold indexes.
 */
class Heap {
  readonly #cells: Value[] = [];

  alloc(value: Value): Addr {
    this.#cells.push(value);
    return (this.#cells.length - 1) as Addr;
  }

  read(addr: Addr): Value {
    return this.#cells[addr]!;
  }

  write(addr: Addr, value: Value): void {
    this.#cells[addr] = value;
  }
}

/**
 * A scope as a cons list of bindings, innermost first, so a name shadows by
 * being nearer and a lookup is the first hit walking outward.
 *
 * A list and not a stack of frames, though it is pushed and popped like one: it
 * is persistent, and that is the property being used rather than an accident of
 * the shape. A closure keeps the list it captured while the scope around it
 * goes on being extended, which is what a copied stack would have to be copied
 * for. TypeScript ships no persistent list, so this is the one written here.
 */
type Binding = {
  readonly name: string | undefined;
  /**
   * Mutable for one reason: a `def` run must be in scope inside its own
   * members, so the bindings are made before the bodies that fill them. See
   * `#tie` for why the hole is never observable.
   */
  value: Value | undefined;
  readonly outer: Scope;
};

export type Scope = Binding | undefined;

/** `_` binds like any other name; nothing can look up a name it has not. */
function bind(scope: Scope, name: BindingIdent, value: Value): Scope {
  return { name: name.text, value, outer: scope };
}

/** Thrown at the stuck term and caught at the boundary. Never caught between. */
class Stuck extends Error {
  constructor(readonly diagnostic: Diagnostic) {
    super(diagnostic.message);
  }
}

function stuck(message: string, at: Position, width = 1): never {
  throw new Stuck(reportError(message, at, width));
}

/**
 * What to call a value in a message about the shape it was not. A kind and not
 * a printing: what went wrong is that a function was wanted and a `Bool` came,
 * and neither of those is the digits of the value.
 */
function describeValue(value: Value): string {
  switch (value.kind) {
    case "VFun":
    case "VPrim":
      return "a function";
    case "VRef":
      return "a cell";
    case "VData":
      return `a ${value.ctor.datatype}`;
  }
}

/**
 * A value as a program would have written it, where it can be. A cell prints as
 * its address and never its contents -- one holding a function that reads it is
 * writable, so following one is not guaranteed to end.
 */
export function valueToString(value: Value): string {
  switch (value.kind) {
    case "VFun":
      return "<function>";
    case "VPrim":
      return `<function ${value.name}>`;
    case "VRef":
      return `<cell ${value.addr}>`;
    case "VData": {
      if (value.ctor.isValue) return value.ctor.name;
      const fields = value.fields.map(valueToString).join(", ");
      return `${value.ctor.name}(${fields})`;
    }
  }
}

/**
 * Applications, which is the only unbounded thing: every loop passes through
 * one, so nothing else has to be counted, and a budget in beta-steps is a
 * number an author can reason about. Divergence is reachable in a *checked*
 * program -- a cell holding a function that reads it, or a negative datatype --
 * so this is not only for the ill-typed ones.
 *
 * Deliberately below what the host stack takes, which is what makes it the
 * limit that actually fires: an application recurses, so a runaway program
 * would otherwise always exhaust the stack first and be told something about
 * the interpreter rather than about itself. Measured at a few thousand for the
 * shallowest shape, and a program nesting its arguments spends more per step,
 * so the margin is wide on purpose. The size is a tuning question, as the
 * subtyper's is; the way out from under the ceiling is an explicit stack.
 */
const FUEL = 2000;

class Evaluator {
  #fuel: number;
  readonly #heap = new Heap();
  /** Constructor by name, last declaration winning, as the checker's seeding does. */
  readonly #ctors = new Map<string, CtorShape>();
  /** Which names a datatype's patterns may use, which is what resolves them. */
  readonly #fields = new Map<string, Set<string>>();

  constructor(decls: readonly TypeDecl[], readonly budget: number) {
    this.#fuel = budget;
    for (const decl of decls) {
      if (decl.kind !== "DatatypeDecl") continue;
      const datatype = decl.name.text;
      const names = new Set<string>();
      for (const ctor of decl.ctors) {
        this.#ctors.set(ctor.name.text, {
          name: ctor.name.text,
          datatype,
          arity: ctor.params?.length ?? 0,
          isValue: ctor.params === undefined,
        });
        names.add(ctor.name.text);
      }
      this.#fields.set(datatype, names);
    }
  }

  /** Builtins, then constructors, so a constructor shadows one -- as in `checkProgram`. */
  #outermost(): Scope {
    const prim = (
      name: string,
      arity: number,
      apply: (args: readonly Value[], at: Position) => Value,
    ): Value => ({ kind: "VPrim", name, arity, apply });

    const addrOf = (value: Value | undefined, at: Position): Addr => {
      if (value === undefined || value.kind !== "VRef") {
        stuck(`expected a cell, found ${describeValue(value!)}`, at);
      }
      return value.addr;
    };

    let scope: Scope = undefined;
    const push = (name: string, value: Value) => {
      scope = { name, value, outer: scope };
    };

    push(
      "ref!",
      prim("ref!", 1, (args) => ({
        kind: "VRef",
        addr: this.#heap.alloc(args[0]!),
      })),
    );
    push(
      "get!",
      prim("get!", 1, (args, at) => this.#heap.read(addrOf(args[0], at))),
    );
    // Answers the value written rather than the cell, so a write is an
    // expression -- which is what its seeded type says.
    push(
      "set!",
      prim("set!", 2, (args, at) => {
        this.#heap.write(addrOf(args[0], at), args[1]!);
        return args[1]!;
      }),
    );

    for (const ctor of this.#ctors.values()) {
      push(
        ctor.name,
        ctor.isValue
          ? { kind: "VData", ctor, fields: [] }
          : prim(ctor.name, ctor.arity, (fields) => ({
            kind: "VData",
            ctor,
            fields,
          })),
      );
    }
    return scope;
  }

  run(term: TermNode): Value {
    return this.#eval(term, this.#outermost());
  }

  #eval(term: TermNode, scope: Scope): Value {
    switch (term.kind) {
      case "Var":
        return this.#lookup(term.name, scope);
      case "Abs":
        return { kind: "VFun", params: term.params, body: term.body, scope };
      // Erased: nothing about a type reaches here, so a type argument that
      // names nothing is not an error a run can have.
      case "TypeApp":
        return this.#eval(term.callee, scope);
      case "App": {
        const callee = this.#eval(term.callee, scope);
        const args = term.args.map((arg) => this.#eval(arg, scope));
        return this.#apply(callee, args, term.at);
      }
      case "Let":
        return this.#eval(
          term.body,
          bind(scope, term.name, this.#eval(term.bound, scope)),
        );
      case "LetRec":
        return this.#eval(term.body, this.#tie(term.defs, scope));
      case "Match":
        return this.#match(term, scope);
    }
  }

  #lookup(name: Ident, scope: Scope): Value {
    for (let binding = scope; binding !== undefined; binding = binding.outer) {
      if (binding.name !== name.text) continue;
      if (binding.value === undefined) {
        stuck(
          `${name.text} is used before it is bound`,
          name.at,
          name.text.length,
        );
      }
      return binding.value;
    }
    stuck(`unknown name ${name.text}`, name.at, name.text.length);
  }

  /**
   * The scope a `def` run introduces, in the three phases `#checkLetRec` uses,
   * because where a name resolves must be the same question there and here.
   *
   * A signature is something the author supplied, so an annotated member is
   * bound before any body runs and is visible to the whole run. An unannotated
   * one has no signature to push and falls back to being a `let`: bound as it
   * is reached, so it sees itself and every member above it, and a *later*
   * unannotated sibling is a name outside the run -- which is what the checker
   * reports as unknown. Binding the whole run at once would resolve that name
   * to the group and quietly mean something else.
   *
   * Every member is left a hole first, and none is observable: a `DefItem`'s
   * bound is an `Abs` by construction, so evaluating one captures the scope
   * without reading it. That is a parser guarantee and not a checker one, which
   * is why it holds here at all.
   */
  #tie(defs: readonly DefItem[], outer: Scope): Scope {
    const annotated: { binding: Binding; def: DefItem }[] = [];
    let scope = outer;

    for (const def of defs) {
      if (def.annotation === undefined) continue;
      const binding: Binding = {
        name: def.name.text,
        value: undefined,
        outer: scope,
      };
      annotated.push({ binding, def });
      scope = binding;
    }

    for (const def of defs) {
      if (def.annotation !== undefined) continue;
      const binding: Binding = {
        name: def.name.text,
        value: undefined,
        outer: scope,
      };
      scope = binding;
      binding.value = this.#eval(def.bound, scope);
    }

    // Last, so a signature's body sees the unannotated members too.
    for (const { binding, def } of annotated) {
      binding.value = this.#eval(def.bound, scope);
    }
    return scope;
  }

  #apply(callee: Value, args: readonly Value[], at: Position): Value {
    // Here and nowhere else, so what the budget counts stays one thing.
    if (this.#fuel-- <= 0) {
      stuck(`evaluation did not finish within ${this.budget} steps`, at);
    }
    switch (callee.kind) {
      case "VFun": {
        if (callee.params.length !== args.length) {
          stuck(
            `expected ${callee.params.length} arguments, found ${args.length}`,
            at,
          );
        }
        let scope = callee.scope;
        for (const [index, param] of callee.params.entries()) {
          scope = bind(scope, param.name, args[index]!);
        }
        return this.#eval(callee.body, scope);
      }
      case "VPrim":
        if (callee.arity !== args.length) {
          stuck(
            `${callee.name} expected ${callee.arity} arguments, found ${args.length}`,
            at,
          );
        }
        return callee.apply(args, at);
      default:
        stuck(`expected a function, found ${describeValue(callee)}`, at);
    }
  }

  #match(term: Extract<TermNode, { kind: "Match" }>, scope: Scope): Value {
    const scrutinee = this.#eval(term.scrutinee, scope);
    if (scrutinee.kind !== "VData") {
      stuck(
        `expected something to match on, found ${describeValue(scrutinee)}`,
        term.scrutinee.at,
      );
    }
    for (const arm of term.arms) {
      const bound = this.#bindPattern(arm.pattern, scrutinee, scope);
      if (bound !== undefined) return this.#eval(arm.body, bound.scope);
    }
    stuck(`no arm matches ${scrutinee.ctor.name}`, term.at);
  }

  /**
   * The scope an arm runs in, or absent where the pattern is for another
   * constructor. Wrapped, since an empty scope is `undefined` too.
   *
   * A name is resolved against the scrutinee's own datatype, as the checker
   * resolves it -- so a constructor of some *other* datatype is a mistake here
   * and not merely an arm that does not fire.
   */
  #bindPattern(
    pattern: MatchPat,
    scrutinee: Extract<Value, { kind: "VData" }>,
    scope: Scope,
  ): { scope: Scope } | undefined {
    if (pattern.kind === "PWild") return { scope };
    const known = this.#fields.get(scrutinee.ctor.datatype);
    if (known === undefined || !known.has(pattern.name.text)) {
      stuck(
        `${pattern.name.text} is not a constructor of ${scrutinee.ctor.datatype}`,
        pattern.name.at,
        pattern.name.text.length,
      );
    }
    if (pattern.name.text !== scrutinee.ctor.name) return undefined;
    if (pattern.args.length !== scrutinee.fields.length) {
      stuck(
        `${pattern.name.text} has ${scrutinee.fields.length} fields, bound ${pattern.args.length}`,
        pattern.at,
      );
    }
    let bound = scope;
    for (const [index, name] of pattern.args.entries()) {
      bound = bind(bound, name, scrutinee.fields[index]!);
    }
    return { scope: bound };
  }
}

/**
 * Run a program, whatever anything else made of it.
 *
 * The diagnostics are zero or one: nothing recovers, so there is no second
 * failure to find. A stack the host cannot grow is reported separately from
 * fuel -- the two have different fixes, and a deep recursion is not a loop.
 */
export function evaluate(
  program: Program,
  budget: number = FUEL,
): Result<Value> {
  const evaluator = new Evaluator(program.decls, budget);
  try {
    return produced(evaluator.run(program.term));
  } catch (thrown) {
    if (thrown instanceof Stuck) return failed([thrown.diagnostic]);
    if (thrown instanceof RangeError) {
      return failed([reportError("evaluation nested too deeply", program.at)]);
    }
    throw thrown;
  }
}
