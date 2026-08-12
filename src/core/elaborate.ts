/**
 * Surface types to internal types: names become identities, aliases disappear,
 * and binders become de Bruijn.
 *
 * A name resolves against the type variables in scope, then the declarations.
 * Only the first step is a choice; aliases and datatypes share one namespace,
 * so the order they are asked in decides nothing.
 *
 * The context is the scope: a binder pushes its type variables, elaborates
 * under them, and closes before `inScope` pops. So `lookupTypeVar` handles
 * shadowing for free and nothing here keeps a second name table.
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

      // Closing the parts at depth 0 is what turns level `mark + j` into
      // `BVar j`. Closing the assembled `TFun` would abstract an *enclosing*
      // binder instead, pushing these indices past their own group.
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
      // The wildcard names nothing, so repeating it is no collision. Still
      // pushed, holding the position its `BVar j` counts on -- unnameable,
      // not absent.
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
   * The first takes a datatype's name and arity, an alias whole, *in source
   * order* -- so the first declaration of a name keeps it whichever kind it
   * was. Sweeping the kinds separately would blame every clash on the alias.
   * The price: an alias sees only what precedes it, which is the rule that
   * already ruled out recursion among aliases.
   *
   * The second elaborates constructor fields against the complete signature
   * table, so a field may name its own datatype or one declared below. No
   * shortlist of winners is needed: `initCtors` refuses a name the first pass
   * gave an alias, and one whose constructors are already in. A loser is still
   * elaborated -- bad types inside it are reported -- but has nowhere to land.
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
    decl: Extract<TypeDecl, { kind: "DatatypeDecl" }>,
  ): DatatypeInfo {
    return {
      name: mkDataName(decl.name.text),
      params: decl.typeParams.map((param) => param.text),
      ctors: [],
      initialized: false,
      at: decl.at,
    };
  }

  /** Elaborate a datatype's constructors under its type parameters. */
  #elaborateCtors(
    decl: Extract<TypeDecl, { kind: "DatatypeDecl" }>,
  ): CtorInfo[] {
    const ctors = this.context.inScope((mark) => {
      this.#bindPlainParams(decl.typeParams);

      // Uniqueness is *within* one datatype: `ctorOf` asks the scrutinee's own
      // datatype for its `Nil`, so two may each have one. `flatMap` so a
      // duplicate drops out rather than leaving a hole -- and dropping it, not
      // the name, keeps a later `| Nil ->` from being a second, quieter error.
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
    // Asked on the way out, so what is asserted is what `Declarations` gets.
    this.context.assertClosed(
      `datatype ${decl.name.text}`,
      ctors.flatMap((ctor) => ctor.fields),
      decl.typeParams.length,
    );
    return ctors;
  }

  /** An alias whole -- there is no second pass for it to be finished in. */
  #elaborateAlias(decl: Extract<TypeDecl, { kind: "AliasDecl" }>): AliasInfo {
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
      params: decl.typeParams.map((param) => param.text),
      body,
      at: decl.at,
    };
  }

  /**
   * Bind every constructor as an ordinary term. A constructor is a *function*
   * of its fields, so saturation follows from arity and there is no constructor
   * term form -- including the nullary case, which is why `True` is written
   * `True()`. See `constructorType`.
   *
   * Being ordinary, they sit outermost and anything of the same name shadows
   * them silently -- a later `let`, or another datatype's constructor, this
   * being the one place two datatypes' names meet. Patterns are unaffected,
   * resolving against the scrutinee's own datatype.
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
