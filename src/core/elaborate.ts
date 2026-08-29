/**
 * Surface types to internal types: names become identities, aliases disappear,
 * and binders become de Bruijn.
 *
 * A name resolves against the type variables in scope, then the declarations.
 * Neither step is really a choice: aliases and datatypes share one namespace,
 * and a binder taking a declared name is reported where it is bound, so no
 * well-formed program can tell the order apart.
 *
 * The context is the scope: a binder pushes its type variables, elaborates
 * under them, and closes before `inScope` pops. So `lookupTypeVar` handles
 * shadowing for free and nothing here keeps a second name table.
 *
 * The variance inference at the foot of the file is the one thing here that
 * reads no surface syntax. It is here because it is the last pass of
 * `elaborateDeclarations`: it walks fields this file has just finished
 * building, into a table only this file fills, and nothing else ever calls it.
 */

import {
  type Diagnostic,
  type Position,
  reportError,
  reportWarning,
} from "../diagnostics/diagnostic.ts";
import {
  type AliasDecl,
  bindingHint,
  type BindingIdent,
  type DatatypeDecl,
  type Ident,
  type TypeDecl,
  type TypeNode,
  type TypeParam,
} from "../syntax/ast.ts";
import type {
  AliasInfo,
  Context,
  CtorInfo,
  DatatypeInfo,
  Declarations,
  ParamInfo,
} from "./context.ts";
import {
  badUnder,
  BVar,
  closeFrom,
  type DataName,
  flip,
  FVar,
  impossible,
  mkDataName,
  mkTypeParamInfo,
  openMany,
  TData,
  TFun,
  TNever,
  TUnknown,
  type Type,
  type TypeParamInfo,
  type Variance,
} from "./types.ts";

export class Elaborator {
  constructor(
    readonly declarations: Declarations,
    readonly context: Context,
    readonly diagnostics: Diagnostic[],
  ) {}

  #report(message: string, at: Position, width = 1): Diagnostic {
    const diagnostic = reportError(message, at, width);
    this.diagnostics.push(diagnostic);
    return diagnostic;
  }

  elaborateType(node: TypeNode): Type {
    switch (node.kind) {
      case "UnknownType":
        return TUnknown;
      case "NeverType":
        return TNever;
      case "NameType":
        return this.#elaborateName(node);
      case "FunType":
        return this.#elaborateFun(node);
    }
  }

  #elaborateName(
    node: Extract<TypeNode, { kind: "NameType" }>,
  ): Type {
    // Elaborated before resolving, so an error inside an argument is reported
    // even when the head turns out to be unresolvable.
    const args = node.args.map((arg) => this.elaborateType(arg));
    const { text, at } = node.name;
    const width = text.length;

    const typeVar = this.context.lookupTypeVar(text);
    if (typeVar !== undefined) {
      if (args.length > 0) {
        return badUnder(
          this.#report(`type variable ${text} takes no arguments`, at, width),
        );
      }
      return FVar(typeVar.level, text);
    }

    const alias = this.declarations.aliasOf(text);
    if (alias !== undefined) {
      const wrong = this.#reportArityMismatch(
        "type alias",
        text,
        alias.params.length,
        args,
        at,
      );
      if (wrong !== undefined) return badUnder(wrong);
      // Transparent: expanded here, so nothing downstream learns aliases exist.
      return openMany(alias.body, args);
    }

    const datatype = this.declarations.datatypeOf(text);
    if (datatype !== undefined) {
      const arity = datatype.params.length;
      const wrong = this.#reportArityMismatch(
        "datatype",
        text,
        arity,
        args,
        at,
      );
      if (wrong !== undefined) return badUnder(wrong);
      return TData(datatype.name, args);
    }

    return badUnder(this.#report(`unknown type ${text}`, at, width));
  }

  /** The diagnostic filed for a wrong count, or `undefined` if it was right. */
  #reportArityMismatch(
    what: string,
    name: string,
    arity: number,
    args: readonly Type[],
    at: Position,
  ): Diagnostic | undefined {
    if (args.length === arity) return undefined;
    return this.#report(
      `${what} ${name} takes ${arity} type argument${
        arity === 1 ? "" : "s"
      }, given ${args.length}`,
      at,
      name.length,
    );
  }

  #elaborateFun(node: Extract<TypeNode, { kind: "FunType" }>): Type {
    const closed = this.context.inScope((mark) => {
      const typeParams = this.bindTypeParams(node.typeParams);
      const params = node.params.map((param) => this.elaborateType(param));
      const result = this.elaborateType(node.result);

      // Closing the parts at depth 0 is what turns level `mark + j` into
      // `BVar j`. Closing the assembled `TFun` would abstract an *enclosing*
      // binder instead, pushing these indices past their own group.
      return TFun(
        typeParams,
        params.map((param) => closeFrom(param, mark)),
        closeFrom(result, mark),
      );
    });
    this.context.assertClosed("function type", [closed]);
    return closed;
  }

  /**
   * Bring a binder group into scope and hand back the core binders it becomes.
   *
   * Bounds are *parallel*: every one is elaborated before any variable of the
   * group is in scope, so a bound may name an enclosing binder but never a
   * member of its own group.
   *
   * One call for a lambda's type parameters and a function type's alike, being
   * the same group under the same rules.
   *
   * Reported here: a name used twice within the group, and one a declaration
   * already holds. The second is not a courtesy -- declarations are the other
   * namespace and nothing shadows them, so such a parameter would be
   * unreachable, and silently.
   */
  bindTypeParams(
    params: readonly TypeParam[],
    decided?: readonly Type[],
  ): TypeParamInfo[] {
    // Bounds already decided, where the caller has more to go on than what is
    // written -- a checking context supplying one an author left out. Deciding
    // is then the caller's whole business, including which of the two wins, so
    // `param.bound` is not consulted. What stays either way is the group:
    // parallel elaboration, and the names.
    const bounds = decided ??
      params.map((param) =>
        param.bound === undefined ? TUnknown : this.elaborateType(param.bound)
      );

    const seen = new Set<string>();
    return params.map((param, j) => {
      const bound = bounds[j] ?? TUnknown;
      const name = param.name.text;
      // A wildcard collides with nothing and is reached by nothing, so it is
      // pushed for its position alone.
      if (name === undefined) {
        this.context.pushTypeVar(bound);
      } else {
        if (seen.has(name)) {
          this.#report(
            `duplicate type parameter ${name}`,
            param.name.at,
            name.length,
          );
        } else this.reportDeclaredName(param.name);
        seen.add(name);
        this.context.pushTypeVar(bound, name);
      }
      return mkTypeParamInfo(bindingHint(param.name), bound);
    });
  }

  /** Report a binder whose name a datatype or alias already holds. */
  reportDeclaredName(binder: BindingIdent): void {
    const name = binder.text;
    if (name === undefined) return;
    if (this.declarations.declaredAt(name) === undefined) return;
    this.#report(`type ${name} is already declared`, binder.at, name.length);
  }

  /** The same, for the unbounded parameters a declaration carries. */
  #bindPlainParams(names: readonly BindingIdent[]): void {
    this.bindTypeParams(names.map((name) => ({ name, at: name.at })));
  }

  /**
   * Build the declaration table in three passes.
   *
   * The first takes a datatype's name and arity, an alias whole, *in source
   * order* -- so the first declaration of a name keeps it whichever kind it
   * was. The price is that an alias sees only what precedes it, which is what
   * rules out recursion among aliases.
   *
   * The second elaborates constructor fields against the complete signature
   * table, so a field may name its own datatype or one declared below. No
   * shortlist of winners is needed: `initCtors` refuses a name the first pass
   * gave away. A loser is still elaborated -- bad types inside it are reported
   * -- but has nowhere to land.
   *
   * The third infers every datatype's variance, which is a property of the
   * whole table at once: two declarations may name each other, so there is no
   * order in which one datatype's fields could be walked to a final answer
   * before the next one's.
   */
  elaborateDeclarations(decls: readonly TypeDecl[]): void {
    for (const decl of decls) {
      this.#reportRedeclaration(
        decl.name,
        decl.kind === "DatatypeDecl"
          ? this.declarations.addDatatype(this.#elaborateSignature(decl))
          : this.declarations.addAlias(this.#elaborateAlias(decl)),
      );
    }

    for (const decl of decls) {
      if (decl.kind !== "DatatypeDecl") continue;
      this.declarations.initCtors(decl.name.text, this.#elaborateCtors(decl));
    }

    // A third pass, and it has to be: variance is a property of the whole
    // table at once, since two datatypes may name each other.
    inferDatatypeVariance(this.declarations.datatypes(), this.diagnostics);
  }

  /** Report `name` if the table refused it in favour of `previous`. */
  #reportRedeclaration(name: Ident, previous: Position | undefined): void {
    if (previous === undefined) return;
    this.#report(
      `type ${name.text} is already declared`,
      name.at,
      name.text.length,
    );
  }

  /** Name and arity, all a constructor field needs to name this datatype. */
  #elaborateSignature(
    decl: DatatypeDecl,
  ): DatatypeInfo {
    return {
      name: mkDataName(decl.name.text),
      params: decl.typeParams.map(mkParamInfo),
      ctors: [],
      initialized: false,
      at: decl.at,
    };
  }

  /** Elaborate a datatype's constructors under its type parameters. */
  #elaborateCtors(
    decl: DatatypeDecl,
  ): CtorInfo[] {
    const ctors = this.context.inScope((mark) => {
      this.#bindPlainParams(decl.typeParams);

      // Uniqueness is *within* one datatype: `ctorOf` asks the scrutinee's own
      // datatype for its `Nil`, so two may each have one. The duplicate drops
      // out and the name stays, so a later `| Nil ->` is not a second error.
      const seen = new Set<string>();
      return decl.ctors.flatMap((ctor): CtorInfo[] => {
        if (seen.has(ctor.name.text)) {
          this.#report(
            `datatype ${decl.name.text} already has a constructor ` +
              ctor.name.text,
            ctor.name.at,
            ctor.name.text.length,
          );
          return [];
        }
        seen.add(ctor.name.text);
        return [{
          name: ctor.name.text,
          // Closed over the datatype's parameters, so a use opens them.
          fields: ctor.params.map((field) =>
            closeFrom(this.elaborateType(field), mark)
          ),
          at: ctor.at,
        }];
      });
    });

    // The arity is a *binder depth*: a field sits under a binder no type node
    // materialises, so a depth-zero check would call every field ill-formed.
    this.context.assertClosed(
      `datatype ${decl.name.text}`,
      ctors.flatMap((ctor) => ctor.fields),
      decl.typeParams.length,
    );
    return ctors;
  }

  /** An alias whole -- there is no second pass for it to be finished in. */
  #elaborateAlias(decl: AliasDecl): AliasInfo {
    // Elaborated before the name is claimed, which is what makes an alias
    // naming itself an `unknown type` rather than an infinite expansion.
    const body = this.context.inScope((mark) => {
      this.#bindPlainParams(decl.typeParams);
      return closeFrom(this.elaborateType(decl.body), mark);
    });
    this.context.assertClosed(
      `type alias ${decl.name.text}`,
      [body],
      decl.typeParams.length,
    );

    return {
      name: decl.name.text,
      params: decl.typeParams.map(bindingHint),
      body,
      at: decl.at,
    };
  }

  /**
   * Bind every constructor as an ordinary term. A constructor is a *function*
   * of its fields, so saturation follows from arity and there is no constructor
   * term form -- except where there is nothing to saturate, and `True` is a
   * plain value of type `Bool`. See `constructorType`.
   *
   * Being ordinary, they sit outermost and anything of the same name shadows
   * them silently -- a later `let`, or another datatype's constructor, this
   * being the one place two datatypes' names meet. Patterns are unaffected,
   * resolving against the scrutinee's own datatype.
   */
  seedConstructors(): void {
    for (const datatype of this.declarations.datatypes()) {
      for (const ctor of datatype.ctors) {
        this.context.pushTermVar(constructorType(datatype, ctor), ctor.name);
      }
    }
  }
}

/**
 * `MkPair : [A, B](A, B) -> Pair[A, B]`, and `True : Bool`.
 *
 * Derived rather than stored, so a constructor's function type and the field
 * types its patterns take apart cannot drift. `fields` are already closed
 * over the datatype's parameters and sit directly under this binder.
 *
 * A constructor with no fields of a datatype with no parameters is a *value*:
 * nothing to apply and nothing to instantiate, so `True` rather than
 * `True()`. Both conditions are needed -- `Nil` of `List[A]` still has a type
 * argument to fix, and the value restriction rules out `[A]List[A]`, so it
 * stays `[A]() -> List[A]` and is written `Nil[Bool]()`.
 */
export function constructorType(
  datatype: DatatypeInfo,
  ctor: CtorInfo,
): Type {
  const result = TData(datatype.name, datatype.params.map((_, j) => BVar(j)));
  if (datatype.params.length === 0 && ctor.fields.length === 0) return result;
  return TFun(
    datatype.params.map((param) => mkTypeParamInfo(param.hint, TUnknown)),
    ctor.fields,
    result,
  );
}

/** Instantiate a constructor's fields at a scrutinee's type arguments. */
export function ctorFieldsAt(
  ctor: CtorInfo,
  args: readonly Type[],
): readonly Type[] {
  return ctor.fields.map((field) => openMany(field, args));
}

/** Instantiate an alias at its arguments. Exported for tests. */
export function aliasBodyAt(
  alias: AliasInfo,
  args: readonly Type[],
): Type {
  return openMany(alias.body, args);
}

/**
 * A declared type parameter before anything is known about how it is used.
 * Invariant to begin with, which `inferDatatypeVariance` replaces once every
 * datatype's fields are in.
 */
function mkParamInfo(name: BindingIdent): ParamInfo {
  return {
    hint: bindingHint(name),
    named: name.text !== undefined,
    at: name.at,
    variance: 0,
  };
}

// ---------------------------------------------------- inferring variance

/**
 * What a datatype's parameters do to its arguments, read off its constructor
 * fields rather than declared.
 *
 * Inferred and not written, because checking a written `+A` needs the same
 * walk that inferring it does -- so the inference is the part we need either
 * way, and an annotation would be a layer on top. The usual reason to demand
 * one is separate compilation, a library's variance being part of its
 * published interface; the require walk is textual and flat, so there is no
 * library boundary here to protect.
 *
 * Run once, after every datatype's constructors are in, and it writes its
 * answer into `ParamInfo.variance`. Everything downstream reads that through
 * `Declarations.argVariance`.
 */

/**
 * The set of positions a parameter was found in -- what the walk accumulates,
 * where a `Variance` is what it carries.
 *
 * The same four points `EVarEntry` keeps, and for the same reason: occurring
 * covariantly *and* contravariantly is what leaves an argument unable to move
 * either way, and occurring nowhere is no direction at all. Merged by `||`
 * componentwise and never composed, which is the whole of the difference from
 * a `Variance`.
 */
type Occurrence = { covariantly: boolean; contravariantly: boolean };

/** One row per datatype, one entry per parameter. */
type Table = ReadonlyMap<DataName, readonly Occurrence[]>;

/**
 * Every parameter of every datatype at the *most permissive* point, which is
 * where the fixed point starts and the only direction it moves from.
 *
 * Optimistic on purpose. Seeding at invariant would be sound and useless --
 * nothing would ever move -- whereas seeding at bivariant and only descending
 * computes the best sound answer. It cannot be wrong about a recursive
 * datatype either: in
 *
 *     datatype Opaque[A] where
 *       | Mk(Opaque[A] -> Bool)
 *
 * `A` occurs only under the recursive occurrence, every round prunes, and the
 * answer is that no program can tell an `Opaque[X]` from an `Opaque[Y]`. That
 * is correct rather than hopeful: soundness for a nominal recursive type is a
 * coinductive property, and the greatest permissive fixed point states it.
 */
function seed(datatypes: readonly DatatypeInfo[]): Map<DataName, Occurrence[]> {
  return new Map(datatypes.map((datatype) => [
    datatype.name,
    datatype.params.map(() => ({
      covariantly: false,
      contravariantly: false,
    })),
  ]));
}

function noteOccurrence(occurrence: Occurrence, variance: Variance): void {
  if (variance >= 0) occurrence.covariantly = true;
  if (variance <= 0) occurrence.contravariantly = true;
}

/** How many flags the table has set, which is what the fixed point counts. */
function flagsSet(table: Table): number {
  let total = 0;
  for (const row of table.values()) {
    for (const occurrence of row) {
      if (occurrence.covariantly) total += 1;
      if (occurrence.contravariantly) total += 1;
    }
  }
  return total;
}

/**
 * Walk one constructor field, merging what it finds into `row`.
 *
 * Entered at `+1`: a field is projected by `match` and never assigned, which
 * is why there is no contravariant entry, and why a mutable cell has to arrive
 * as a builtin rather than as a datatype this walk would have to model.
 *
 * `depth` tracks binders the way `openAt` does, because a field may hold a
 * function type of its own and those `BVar`s are not the datatype's. `snapshot`
 * is last round's table, read and never written -- see `inferDatatypeVariance`.
 */
function noteField(
  type: Type,
  depth: number,
  variance: Variance,
  row: readonly Occurrence[],
  snapshot: Table,
): void {
  switch (type.kind) {
    case "TUnknown":
    case "TNever":
    case "TBad":
    case "FVar":
      return;

    case "BVar": {
      // Bound by a binder inside the field, so it is none of the datatype's
      // parameters.
      if (type.index < depth) return;
      const occurrence = row[type.index - depth] ??
        impossible("a field closed over its datatype's parameters");
      noteOccurrence(occurrence, variance);
      return;
    }

    case "TFun": {
      const inner = depth + type.typeParams.length;
      const flipped = flip(variance);
      // Bounds are parallel, so they stay at `depth`; both they and the
      // parameters are contravariant, and the result alone is not.
      for (const binder of type.typeParams) {
        noteField(binder.bound, depth, flipped, row, snapshot);
      }
      for (const param of type.params) {
        noteField(param, inner, flipped, row, snapshot);
      }
      noteField(type.result, inner, variance, row, snapshot);
      return;
    }

    case "TData": {
      // Reading the table here is what makes this walk terminate on a
      // recursive datatype: `Foo[X]` recurses into `X`, a proper subterm, and
      // never unfolds `Foo`. Only the *table* iterates.
      const target = snapshot.get(type.name);
      type.args.forEach((arg, i) => {
        // An undeclared name is already reported; invariance asks the least of
        // this walk and so concludes the least.
        const occurrence = target?.[i] ??
          { covariantly: true, contravariantly: true };
        // Four ways to go on, and the fourth is why nothing here has to
        // compose two occurrences or flip one. A parameter nothing observes
        // contributes nothing, so the sub-walk is dropped rather than run at
        // some position it would then have to invent.
        if (occurrence.covariantly && occurrence.contravariantly) {
          noteField(arg, depth, 0, row, snapshot);
        } else if (occurrence.covariantly) {
          noteField(arg, depth, variance, row, snapshot);
        } else if (occurrence.contravariantly) {
          noteField(arg, depth, flip(variance), row, snapshot);
        }
      });
      return;
    }
  }
}

/** Every field of every datatype, once, against `snapshot`. */
function oneRound(
  datatypes: readonly DatatypeInfo[],
  snapshot: Table,
): Map<DataName, Occurrence[]> {
  const fresh = seed(datatypes);
  for (const datatype of datatypes) {
    const row = fresh.get(datatype.name) ?? impossible("a row per datatype");
    for (const ctor of datatype.ctors) {
      for (const field of ctor.fields) {
        noteField(field, 0, 1, row, snapshot);
      }
    }
  }
  return fresh;
}

/**
 * Infer every datatype's variance and write it into its parameters.
 *
 * The fixed point is **global over the table, not per datatype**: two
 * declarations may name each other, so this is one iteration over every
 * parameter of every one of them.
 *
 * It cannot diverge, so unlike subtyping it takes no fuel. Positions only ever
 * descend and a merge only ever sets a flag, so the number of flags set across
 * the whole table is a non-decreasing integer bounded by `2n` for `n`
 * parameters in all -- which is both the stopping criterion and the
 * termination argument: at most `2n` rounds change anything and one more
 * notices.
 *
 * Each round reads last round's table and writes a fresh one (Jacobi) rather
 * than updating in place. In place reaches the same fixed point and often
 * sooner, but the round *counts* are then implementation-defined, and those
 * counts are what catches a one-pass bug: round 1 of a recursive datatype is a
 * complete, plausible, unsound answer, because every recursive occurrence was
 * still being pruned.
 */
export function inferDatatypeVariance(
  datatypes: readonly DatatypeInfo[],
  diagnostics: Diagnostic[],
): void {
  let table: Table = seed(datatypes);
  for (let flags = 0;;) {
    const next = oneRound(datatypes, table);
    table = next;
    const grown = flagsSet(next);
    if (grown === flags) break;
    flags = grown;
  }

  for (const datatype of datatypes) {
    const row = table.get(datatype.name) ?? impossible("a row per datatype");
    datatype.params.forEach((param, j) => {
      const occurrence = row[j] ?? impossible("an entry per parameter");
      param.variance = varianceOf(occurrence);
      if (isPhantom(occurrence) && param.named && !anyFieldIsBad(datatype)) {
        diagnostics.push(reportWarning(
          `nothing observes the type parameter ${param.hint} of ` +
            `${datatype.name}, so it makes no difference to the type; write ` +
            `it \`_\` if that is meant`,
          param.at,
          param.hint.length,
        ));
      }
    });
  }
}

/**
 * A position read back as a `Variance`, which has to answer for bivariance and
 * has no point to answer with. It collapses to covariant: sound, and
 * incomplete only for a parameter no program can observe -- which is what the
 * phantom warning says instead, once, at the declaration that knows.
 */
function varianceOf(occurrence: Occurrence): Variance {
  if (occurrence.covariantly && occurrence.contravariantly) return 0;
  if (occurrence.contravariantly) return -1;
  return 1;
}

function isPhantom(occurrence: Occurrence): boolean {
  return !occurrence.covariantly && !occurrence.contravariantly;
}

/**
 * Whether anything in this datatype failed to elaborate. A field that did
 * stands as `<bad>` with a report already made, and a parameter that occurred
 * only there then looks unused -- so the phantom warning is dropped for the
 * whole declaration rather than blaming the author twice for one mistake. The
 * inference itself still runs.
 */
function anyFieldIsBad(datatype: DatatypeInfo): boolean {
  const holdsBad = (type: Type): boolean => {
    switch (type.kind) {
      case "TBad":
        return true;
      case "TFun":
        return type.typeParams.some((binder) => holdsBad(binder.bound)) ||
          type.params.some(holdsBad) || holdsBad(type.result);
      case "TData":
        return type.args.some(holdsBad);
      default:
        return false;
    }
  };
  return datatype.ctors.some((ctor) => ctor.fields.some(holdsBad));
}
