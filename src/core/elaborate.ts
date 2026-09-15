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
  nowhere,
  type Position,
  reportError,
  reportWarning,
} from "../diagnostics/diagnostic.ts";
import {
  type AliasDecl,
  bindingHint,
  type BindingIdent,
  type CtorDecl,
  type DatatypeDecl,
  type Ident,
  type TypeDecl,
  type TypeNode,
  type TypeParam,
} from "../syntax/ast.ts";
import type {
  AliasInfo,
  Context,
  DataCtorInfo,
  DataParamInfo,
  DatatypeInfo,
  Declarations,
} from "./context.ts";
import {
  badUnder,
  BVar,
  closeFrom,
  flip,
  FVar,
  impossible,
  mkTypeParamInfo,
  openMany,
  TData,
  TFun,
  TNever,
  TRef,
  TUnknown,
  type Type,
  type TypeParamInfo,
  type Variance,
} from "./types.ts";

/** What a declaration with nothing to claim claimed. */
const NO_NAMES: ReadonlySet<string> = new Set();

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
      // The one node standing for something unwritten. A `def` parameter has no
      // other source, so the omission is an error wherever the parameter is
      // read, and `bad` is what a reader gets once it is reported.
      case "MissingParamType": {
        const hint = bindingHint(node.name);
        return badUnder(this.#report(
          `cannot infer a type for ${hint}: a def's parameters must be ` +
            `annotated, nothing else can supply them`,
          node.at,
          hint.length,
        ));
      }
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
      return TData(datatype, args);
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
      // The name is dropped here and nowhere else -- see `DomainType`.
      const params = node.params.map((param) => this.elaborateType(param.type));
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
    // Where the caller has more to go on than what is written -- a checking
    // context supplying a bound an author left out -- deciding is the caller's
    // whole business, including which of the two wins, so `param.bound` is not
    // consulted at all.
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
   * shortlist of winners is needed: `fillCtors` refuses a name the first pass
   * gave away. A loser is still elaborated -- bad types inside it are reported
   * -- but has nowhere to land.
   *
   * The third infers every datatype's variance, which is a property of the
   * whole table at once: two declarations may name each other, so there is no
   * order in which one datatype's fields could be walked to a final answer
   * before the next one's.
   */
  elaborateDeclarations(decls: readonly TypeDecl[]): void {
    // What the first phase claimed, for the second to elaborate. The list and
    // not `decls` again: a refused constructor name is a report against the
    // declaration, filed a phase before the one that measures them.
    const claimed: {
      decl: DatatypeDecl;
      taken: ReadonlySet<string>;
      reported: boolean;
    }[] = [];
    for (const decl of decls) {
      if (decl.kind !== "DatatypeDecl") {
        this.#reportRedeclaration(
          decl.name,
          this.declarations.addAlias(this.#elaborateAlias(decl)),
        );
        continue;
      }
      const info = this.#elaborateSignature(decl);
      const previous = this.declarations.addDatatype(info);
      this.#reportRedeclaration(decl.name, previous);
      // A declaration that lost its own name claims nothing else. Its
      // constructors would be types of a family the table does not have --
      // reachable, since a type name is enough to write one, and inhabited by
      // nothing, since `fillCtors` refuses the cases behind them. It is still
      // elaborated below, which is where a bad type inside it is reported.
      claimed.push(
        previous === undefined
          ? { decl, ...this.#claimCtorNames(decl, info) }
          : { decl, taken: NO_NAMES, reported: true },
      );
    }

    for (const { decl, taken, reported } of claimed) {
      // Measured here because nothing read back off the field types answers
      // it -- see `DatatypeInfo.ctorsReported`.
      const before = this.diagnostics.length;
      const ctors = this.#elaborateCtors(decl, taken);
      this.declarations.fillCtors(
        decl.name.text,
        ctors,
        reported || this.diagnostics.length > before,
      );
    }

    inferDatatypeVariance(this.declarations.datatypes(), this.diagnostics);
  }

  /**
   * Claim each constructor's name as a type of its own, in the phase that
   * claims datatype names -- so a field written in this same run may mention
   * `Cons[A]`, exactly as it may mention `List[A]`.
   *
   * The entry is a datatype in every respect but declaring one: its family is
   * the datatype above it, and its parameters are that declaration's *own
   * array*, so `Cons[A]` is saturated by the arity `List` was written with and
   * moves the way variance inference decides `List`'s argument moves. Its
   * single case is filled when the constructors are.
   *
   * Two constructors claim nothing: one written as a bare name, and one of its
   * own datatype's name -- which is refused where it would have to claim. See
   * the loop.
   *
   * This is where a constructor name stops being private to its datatype. Two
   * datatypes may no longer each declare a `Nil`, and a duplicate within one
   * declaration is refused by the same rule rather than by a check of its own.
   * A bare name is private still, having claimed nothing, so its only rule is
   * the declaration's own -- which is why this answers whether anything was
   * refused
   * -- which is why the answer is whether anything was refused: that is a
   * report standing against the declaration, and the phase that measures them
   * runs after this one.
   */
  #claimCtorNames(
    decl: DatatypeDecl,
    info: DatatypeInfo,
  ): { taken: ReadonlySet<string>; reported: boolean } {
    let reported = false;
    const seen = new Set<string>();
    const taken = new Set<string>();
    for (const ctor of decl.ctors) {
      // A declaration may not repeat a name, whichever forms the two were
      // written in: `| On` beside `| On()` is one case written twice, and the
      // second is dropped by the pass below. Asked first and of every form,
      // because what claims a type no longer answers it -- half these names
      // reach the table and half do not.
      if (seen.has(ctor.name.text)) {
        this.#report(
          `constructor ${ctor.name.text} is already declared`,
          ctor.name.at,
          ctor.name.text.length,
        );
        reported = true;
        continue;
      }
      seen.add(ctor.name.text);
      // A bare name claims no *type*. Either it declares a value, and a value
      // builds nothing, so the type would be one no term could ever have -- or
      // the datatype takes parameters and the form is refused, where a report
      // already stands. One test for both, and which it was stays in
      // `#reportValueCtor`, the phase that can answer it.
      if (ctor.params === undefined) continue;
      if (ctor.name.text === info.name) {
        // A sole constructor of its datatype's name is not a second type: the
        // two have the same family and the same one case, so they *are* the
        // same type and there is nothing to claim. `datatype Box where
        // | Box(Bool)` is the wrapper this makes ordinary.
        if (decl.ctors.length === 1) continue;
        this.#report(
          `constructor ${ctor.name.text} may take its datatype's name only ` +
            `where it is the only one`,
          ctor.name.at,
          ctor.name.text.length,
        );
        reported = true;
        continue;
      }
      const previous = this.declarations.addDatatype({
        name: ctor.name.text,
        family: info.name,
        params: info.params,
        ctors: [],
        ctorsReported: false,
        ctorsFilled: false,
        at: ctor.at,
      });
      this.#reportRedeclaration(ctor.name, previous);
      if (previous === undefined) continue;
      // First come, first served, and all the way: the name is another
      // declaration's, so this is not a case of this datatype either. Kept as
      // a case it would be the one constructor whose name is a type some
      // other family holds, which is no state the language has.
      taken.add(ctor.name.text);
      reported = true;
    }
    return { taken, reported };
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
      name: decl.name.text,
      family: decl.name.text,
      params: decl.typeParams.map(mkDataParamInfo),
      ctors: [],
      ctorsReported: false,
      ctorsFilled: false,
      at: decl.at,
    };
  }

  /**
   * Elaborate a datatype's constructors under its type parameters, dropping
   * the ones whose names went elsewhere.
   *
   * `taken` is first-come-first-served carried through: a name belongs to the
   * declaration that claimed it, and a case here under that name would be a
   * constructor whose name means another datatype's type -- so it is not one
   * of this datatype's cases at all. Elaborated before it is dropped, because
   * a bad type written inside it is still a mistake worth reporting, which is
   * how a losing *declaration* is treated a phase down.
   */
  #elaborateCtors(
    decl: DatatypeDecl,
    taken: ReadonlySet<string>,
  ): DataCtorInfo[] {
    const ctors = this.context.inScope((mark) => {
      this.#bindPlainParams(decl.typeParams);

      // The duplicate drops out and the name stays, so a later `| Nil ->` is
      // not a second error. Dropped silently: names are claimed a phase
      // earlier now, so a report already stands against this one.
      const seen = new Set<string>();
      return decl.ctors.flatMap((ctor): DataCtorInfo[] => {
        if (seen.has(ctor.name.text)) return [];
        seen.add(ctor.name.text);
        const one: DataCtorInfo = {
          name: ctor.name.text,
          // Closed over the datatype's parameters, so a use opens them.
          fields: (ctor.params ?? []).map((field) =>
            closeFrom(this.elaborateType(field.type), mark)
          ),
          isValue: this.#reportValueCtor(ctor, decl),
          at: ctor.at,
        };
        return taken.has(one.name) ? [] : [one];
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

  /**
   * Whether a constructor written as a bare name may be the value it asks to
   * be, reporting it where it may not.
   *
   * A value has one type, and `Nil` of `List[A]` would need `[A]List[A]` -- a
   * quantifier over a non-function, which is the value restriction. So the form
   * is refused on a parameterised datatype and the constructor stands as the
   * function it would have been anyway, which is what `Nil[Bool]()` already
   * expects to find.
   */
  #reportValueCtor(ctor: CtorDecl, decl: DatatypeDecl): boolean {
    if (ctor.params !== undefined) return false;
    if (decl.typeParams.length === 0) return true;
    const name = ctor.name.text;
    this.#report(
      `${name} is declared as a value, but ${decl.name.text} takes type ` +
        `parameters, so it has no one type -- write ${name}() instead`,
      ctor.name.at,
      name.length,
    );
    return false;
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
    for (const family of this.declarations.datatypes()) {
      for (const ctor of family.ctors) {
        const built = this.declarations.datatypeBuiltBy(family, ctor);
        this.context.pushTermVar(constructorType(built, ctor), ctor.name);
      }
    }
  }

  /**
   * `Ref` and the three operations over it, before the program's own
   * declarations.
   *
   * The type is seeded as a *transparent alias* for the former, which is
   * exactly what an alias is -- expanded during elaboration, with nothing
   * downstream learning it existed. Its body is one this language has no
   * syntax for, and that is the only thing unusual about it.
   *
   * A name and not a keyword, so `Ref` obeys whatever rule every other type
   * name obeys -- being taken, being refused to a type parameter, being
   * reported at the wrong arity -- by machinery that was already there. If type
   * names are ever made shadowable, this one follows without being revisited.
   *
   *     ref! : [T](T) -> Ref[T]
   *     get! : [T](Ref[T]) -> T
   *     set! : [T](Ref[T], T) -> T
   *
   * `set!` answers the value written rather than the cell, so a write is an
   * expression with the type its right-hand side had, and nothing has to be
   * read back to use it.
   *
   * Built here rather than parsed from a prelude, which would need a `Ref` a
   * program could declare -- and the point of a type former is that none can.
   *
   * The `!` marks these as the operations that will have an effect once there
   * is an evaluator to have it in. Nothing enforces the convention; what
   * reserves the spelling is that the parser admits a bang at no position where
   * a name is bound.
   */
  seedBuiltins(): void {
    const T = BVar(0);
    const cell = TRef(T);
    this.declarations.addAlias({
      name: "Ref",
      params: ["T"],
      body: cell,
      at: nowhere,
    });
    const over = (params: readonly Type[], result: Type) =>
      TFun([mkTypeParamInfo("T", TUnknown)], params, result);
    const builtins: readonly (readonly [string, Type])[] = [
      ["ref!", over([T], cell)],
      ["get!", over([cell], T)],
      ["set!", over([cell, T], T)],
    ];
    for (const [name, type] of builtins) this.context.pushTermVar(type, name);
  }
}

/**
 * `Cons : [A](A, List[A]) -> Cons[A]`, and `True : Bool`.
 *
 * The result is built from the `datatype` it is handed, which is the caller's
 * choice of what this constructor answers with -- `Declarations.datatypeBuiltBy`
 * makes it, and the parameters are the family's either way.
 *
 * Derived rather than stored, so a constructor's function type and the field
 * types its patterns take apart cannot drift. `fields` are already closed
 * over the datatype's parameters and sit directly under this binder.
 *
 * Which of the two it is comes from the *declaration*: `| True` is a value and
 * `| True()` a function of no arguments, both legal on a monomorphic datatype.
 * Read off `isValue` rather than from the arity, which cannot tell them apart
 * -- and cannot be asked to, `Nil` of `List[A]` being nullary and still a
 * function, since the value restriction rules out the `[A]List[A]` it would
 * otherwise have. So it stays `[A]() -> List[A]` and is written `Nil[Bool]()`.
 */
export function constructorType(
  datatype: DatatypeInfo,
  ctor: DataCtorInfo,
): Type {
  const result = TData(datatype, datatype.params.map((_, j) => BVar(j)));
  if (ctor.isValue) return result;
  return TFun(
    datatype.params.map((param) => mkTypeParamInfo(param.hint, TUnknown)),
    ctor.fields,
    result,
  );
}

/** Instantiate a constructor's fields at a scrutinee's type arguments. */
export function ctorFieldsAt(
  ctor: DataCtorInfo,
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
function mkDataParamInfo(name: BindingIdent): DataParamInfo {
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
 * Inferred and not written, because checking a written `+A` needs the same walk
 * that inferring it does, so an annotation would be a layer on top of the part
 * needed either way. The usual reason to demand one is separate compilation,
 * where a library's variance is part of its published interface; the require
 * walk is textual and flat, so there is no such boundary to protect.
 *
 * Run once, after every datatype's constructors are in, and it writes its
 * answer into `DataParamInfo.variance`, which every `TData` of that datatype
 * already holds by reference -- so this pass makes the answer visible to every
 * node built before it ran.
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

/**
 * One row per datatype, one entry per parameter -- and one table for the whole
 * fixed point, read and written in place. Neither the map nor a row is ever
 * replaced; only the flags move, and only ever from false to true.
 */
type Table = ReadonlyMap<string, readonly Occurrence[]>;

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
function seed(datatypes: readonly DatatypeInfo[]): Map<string, Occurrence[]> {
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
 * `depth` tracks binders the way `openWith` does, because a field may hold a
 * function type of its own and those `BVar`s are not the datatype's. `row` is
 * this datatype's entry in `table` and the only thing written -- and `table` is
 * that same table, so a `TData` may read a row this round has already moved,
 * its own included.
 */
function noteField(
  type: Type,
  depth: number,
  variance: Variance,
  row: readonly Occurrence[],
  table: Table,
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
        noteField(binder.bound, depth, flipped, row, table);
      }
      for (const param of type.params) {
        noteField(param, inner, flipped, row, table);
      }
      noteField(type.result, inner, variance, row, table);
      return;
    }

    // A cell's argument is invariant, and says so itself -- there is no
    // declaration to consult and so no round in which the answer could still
    // be moving.
    case "TRef":
      noteField(type.arg, depth, 0, row, table);
      return;

    case "TData": {
      // Reading the table here is what makes this walk terminate on a
      // recursive datatype: `Foo[X]` recurses into `X`, a proper subterm, and
      // never unfolds `Foo`. Only the *table* iterates.
      const target = table.get(type.name);
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
          noteField(arg, depth, 0, row, table);
        } else if (occurrence.covariantly) {
          noteField(arg, depth, variance, row, table);
        } else if (occurrence.contravariantly) {
          noteField(arg, depth, flip(variance), row, table);
        }
      });
      return;
    }
  }
}

/** Every field of every datatype, once, merged into `table` as it goes. */
function oneRound(datatypes: readonly DatatypeInfo[], table: Table): void {
  for (const datatype of datatypes) {
    const row = table.get(datatype.name) ?? impossible("a row per datatype");
    for (const ctor of datatype.ctors) {
      for (const field of ctor.fields) {
        noteField(field, 0, 1, row, table);
      }
    }
  }
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
 * One table, read and written in place: a field sees what the fields before it
 * found. Sound for the same reason the whole thing is -- the walk only sets
 * flags, so a row that has already moved concludes at least as much as the row
 * it moved from, and the least fixed point above the seed is the same either
 * way. Only the round count changes, and only downwards.
 *
 * Which makes a round count declaration-order dependent, and so worth nothing
 * on its own: a recursive occurrence read after the fields that decide it
 * settles a pass earlier than one read before them. Nothing asserts a count.
 * `docs/variance.md` §6 has the traces, and says why an example meant to catch
 * a checker that never loops has to write its recursive constructor first.
 */
export function inferDatatypeVariance(
  datatypes: readonly DatatypeInfo[],
  diagnostics: Diagnostic[],
): void {
  const table = seed(datatypes);
  for (let flags = 0;;) {
    oneRound(datatypes, table);
    const grown = flagsSet(table);
    if (grown === flags) break;
    flags = grown;
  }

  for (const datatype of datatypes) {
    const row = table.get(datatype.name) ?? impossible("a row per datatype");
    datatype.params.forEach((param, j) => {
      const { covariantly, contravariantly } = row[j] ??
        impossible("an entry per parameter");

      // Read back as a `Variance`, which has to answer for bivariance and has
      // no point to answer with. It collapses to covariant: sound, and
      // incomplete only for a parameter no program can observe -- which is
      // what the warning below says instead, once, at the declaration that
      // knows.
      param.variance = covariantly && contravariantly
        ? 0
        : contravariantly
        ? -1
        : 1;

      // A phantom: observed by nothing, transitively. Not reported for a
      // wildcard, which is how an author says a parameter is deliberately
      // unobserved, nor where a report already stands against the declaration
      // -- a parameter occurring only in a field that failed to elaborate
      // looks unused, and one mistake should not be blamed twice.
      if (
        !covariantly && !contravariantly && param.named &&
        !datatype.ctorsReported
      ) {
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
