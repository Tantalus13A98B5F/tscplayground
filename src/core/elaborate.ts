/**
 * Surface types to internal types: names become identities, aliases disappear,
 * and binders become de Bruijn.
 *
 * Resolution walks three namespaces in order -- type variable, alias, datatype.
 * A type variable wins because it is the innermost binding; alias before
 * datatype never matters, since `Declarations` refuses to hold one name twice.
 *
 * The context is the scope. Elaborating a binder pushes type variables, elaborates
 * underneath them, and truncates -- so `lookupTypeVar` handles shadowing for
 * free, and nothing here keeps a second name table.
 */

import {
  type Diagnostic,
  type Position,
  reportError,
} from "../diagnostics/diagnostic.ts";
import type { Ident, TypeDecl, TypeNode, TypeParam } from "../syntax/ast.ts";
import { WILDCARD } from "../syntax/parser.ts";
import type { Context } from "./context.ts";
import type {
  AliasInfo,
  CtorInfo,
  DatatypeInfo,
  Declarations,
} from "./declarations.ts";
import {
  BVar,
  closeFrom,
  FVar,
  type Level,
  mkBinder,
  mkDataName,
  openMany,
  TBad,
  TData,
  TFun,
  TNever,
  TUnknown,
  type Type,
} from "./types.ts";

export class Elaborator {
  constructor(
    readonly declarations: Declarations,
    readonly context: Context,
    readonly diagnostics: Diagnostic[],
  ) {}

  #report(message: string, at: Position, width = 1): void {
    this.diagnostics.push(reportError(message, at, width));
  }

  elaborateType(node: TypeNode): Type {
    switch (node.kind) {
      case "UnknownType":
        return TUnknown;
      case "NeverType":
        return TNever;
      case "BadType":
        return TBad;
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
        this.#report(`type variable ${text} takes no arguments`, at, width);
        return TBad;
      }
      return FVar(typeVar.level, text);
    }

    const alias = this.declarations.aliasOf(text);
    if (alias !== undefined) {
      if (
        !this.#checkArity("type alias", text, alias.params.length, args, at)
      ) {
        return TBad;
      }
      // Transparent: expanded here, so nothing downstream learns aliases exist.
      return openMany(alias.body, args);
    }

    const datatype = this.declarations.datatypeOf(text);
    if (datatype !== undefined) {
      const arity = datatype.params.length;
      if (!this.#checkArity("datatype", text, arity, args, at)) return TBad;
      return TData(datatype.name, args);
    }

    this.#report(`unknown type ${text}`, at, width);
    return TBad;
  }

  #checkArity(
    what: string,
    name: string,
    arity: number,
    args: readonly Type[],
    at: Position,
  ): boolean {
    if (args.length === arity) return true;
    this.#report(
      `${what} ${name} takes ${arity} type argument${
        arity === 1 ? "" : "s"
      }, given ${args.length}`,
      at,
      name.length,
    );
    return false;
  }

  #elaborateFun(node: Extract<TypeNode, { kind: "FunType" }>): Type {
    // Bounds are *parallel*: elaborated before the group is in scope, so one
    // may name an enclosing binder but never a member of its own group.
    const bounds = node.typeParams.map((param) =>
      param.bound === undefined ? TUnknown : this.elaborateType(param.bound)
    );

    const closed = this.context.inScope((mark) => {
    this.#bindTypeParams(node.typeParams, bounds);
    const params = node.params.map((param) => this.elaborateType(param));
    const result = this.elaborateType(node.result);

      // Closing at depth 0 is what makes level `mark + j` into `BVar j`.
      // Closing the assembled `TFun` instead would be wrong: that abstracts an
    // *enclosing* binder, and would push these indices past their own group.
      return TFun(
      node.typeParams.map((param, j) =>
        mkBinder(param.name.text, bounds[j] ?? TUnknown)
      ),
        params.map((param) => closeFrom(param, mark)),
        closeFrom(result, mark),
    );
    });
    this.context.assertClosed("function type", [closed]);
    return closed;
  }

  /** Push a binder group, reporting a name used twice within it. */
  #bindTypeParams(
    params: readonly TypeParam[],
    bounds: readonly Type[],
  ): readonly Level[] {
    const seen = new Set<string>();
    return params.map((param, j) => {
      const { text, at } = param.name;
      // The wildcard is exempt: it names nothing, so repeating it is not a
      // collision. It is still pushed, holding the position its `BVar j`
      // depends on -- unnameable, not absent.
      if (text !== WILDCARD && seen.has(text)) {
        this.#report(
          `duplicate type parameter ${text}`,
          at,
          text.length,
        );
      }
      seen.add(text);
      return this.context.pushTypeVar(text, bounds[j] ?? TUnknown);
    });
  }

  /** The same, for the unbounded parameters a declaration carries. */
  #bindPlainParams(names: readonly Ident[]): readonly Level[] {
    return this.#bindTypeParams(
      names.map((name) => ({ name, at: name.at })),
      names.map(() => TUnknown),
    );
  }

  /**
   * Build the declaration table in two passes.
   *
   * Datatype signatures are collected first, so a constructor field may name
   * its own datatype -- `Cons(A, List[A])` -- or one declared further down.
   * Aliases are added as they are reached, so an alias can only name earlier
   * ones, which rules out recursion among them by construction.
   */
  elaborateDeclarations(decls: readonly TypeDecl[]): void {
    for (const decl of decls) {
      if (decl.kind !== "DatatypeDecl") continue;
      if (this.#reportRedeclaration(decl.name)) continue;
      this.declarations.addDatatype({
        name: mkDataName(decl.name.text),
        params: decl.typeParams.map((param) => param.text),
        ctors: [],
        at: decl.at,
      });
    }

    for (const decl of decls) {
      if (decl.kind === "DatatypeDecl") {
        this.#elaborateDatatype(decl);
      } else {
        this.#elaborateAlias(decl);
      }
    }
  }

  /** True if `name` is already taken, having reported it. */
  #reportRedeclaration(name: Ident): boolean {
    if (!this.declarations.declares(name.text)) return false;
    this.#report(
      `type ${name.text} is already declared`,
      name.at,
      name.text.length,
    );
    return true;
  }

  #elaborateDatatype(
    decl: Extract<TypeDecl, { kind: "DatatypeDecl" }>,
  ): void {
    const signature = this.declarations.datatypeOf(decl.name.text);
    // Absent only if the name was a redeclaration, already reported.
    if (signature === undefined || signature.at !== decl.at) return;

    const count = decl.typeParams.length;
    const ctors = this.context.inScope((mark) => {
    this.#bindPlainParams(decl.typeParams);
      return this.#elaborateCtors(decl, mark);
    });

    // The arity here is a *binder depth*, and outlives the count `closeFrom`
    // shed: a field is stored under a binder no type node materialises, so
    // `BVar j` is parameter j with nothing on hand to say so, and a depth-zero
    // check would call every field ill-formed. Asked here, on the way out --
    // what is asserted is what is handed to `Declarations`.
    this.context.assertClosed(
      `datatype ${decl.name.text}`,
      ctors.flatMap((ctor) => ctor.fields),
      count,
    );
    this.declarations.addDatatype({ ...signature, ctors });
  }

  /** Elaborate a datatype's constructors, its parameters already bound. */
  #elaborateCtors(
    decl: Extract<TypeDecl, { kind: "DatatypeDecl" }>,
    mark: number,
  ): CtorInfo[] {
    const ctors: CtorInfo[] = [];
    for (const ctor of decl.ctors) {
      // Non-fatal, like every other redeclaration: the name keeps pointing at
      // the first constructor to claim it, this one is left out of the
      // datatype, and elaboration carries on to the fields below. Dropping the
      // *duplicate* rather than the name is what keeps a later `| Nil ->` from
      // becoming a second, quieter error.
      if (
        this.declarations.claimCtorName(ctor.name.text, ctor.name.at) !==
          undefined
      ) {
        this.#report(
          `constructor ${ctor.name.text} is already declared`,
          ctor.name.at,
          ctor.name.text.length,
        );
        continue;
      }
      ctors.push({
        name: ctor.name.text,
        // Closed over the datatype's parameters, so a use opens them.
        fields: ctor.params.map((field) =>
          closeFrom(this.elaborateType(field), mark)
        ),
        at: ctor.at,
      });
    }
    return ctors;
  }

  #elaborateAlias(decl: Extract<TypeDecl, { kind: "AliasDecl" }>): void {
    if (this.#reportRedeclaration(decl.name)) return;

    const body = this.context.inScope((mark) => {
    this.#bindPlainParams(decl.typeParams);
      return closeFrom(this.elaborateType(decl.body), mark);
    });
    this.context.assertClosed(
      `type alias ${decl.name.text}`,
      [body],
      decl.typeParams.length,
    );

    this.declarations.addAlias({
      name: decl.name.text,
      params: decl.typeParams.map((param) => param.text),
      body,
      at: decl.at,
    });
  }

  /**
   * Bind every constructor as an ordinary term. A constructor is a *function*
   * of its fields, so saturation follows from arity and there is no constructor
   * term form -- including the nullary case, which is why `True` is written
   * `True()`. See `constructorType`.
   */
  seedConstructors(): void {
    for (const datatype of this.declarations.datatypes()) {
      for (const ctor of datatype.ctors) {
        this.context.pushTermVar(ctor.name, constructorType(datatype, ctor));
      }
    }
  }
}

/**
 * `MkPair : [A, B](A, B) -> Pair[A, B]`.
 *
 * Derived rather than stored, so a constructor's function type and the field
 * types its patterns take apart cannot drift. `fields` are already closed over
 * the datatype's parameters, and they sit directly under this binder, so they
 * need no shifting.
 */
export function constructorType(
  datatype: DatatypeInfo,
  ctor: CtorInfo,
): Type {
  return TFun(
    datatype.params.map((param) => mkBinder(param, TUnknown)),
    ctor.fields,
    TData(datatype.name, datatype.params.map((_, j) => BVar(j))),
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
