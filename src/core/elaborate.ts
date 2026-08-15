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
 */

import {
  type Diagnostic,
  type Position,
  reportError,
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
  mkDataName,
  mkTypeParamInfo,
  openMany,
  TBad,
  TData,
  TFun,
  TNever,
  TUnknown,
  type Type,
  type TypeParamInfo,
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
   * The three steps are one call because a lambda's type parameters and a
   * function type's are the same group under the same rules. Split, each side
   * elaborated the bounds and built the binders for itself, and only the
   * middle step -- the one with the reporting in it -- was ever shared.
   *
   * Reported here: a name used twice within the group, and one a declaration
   * already holds. The second is not a courtesy -- declarations are the other
   * namespace and nothing shadows them, so such a parameter would be
   * unreachable, and silently, `#elaborateName` asking the context first.
   */
  bindTypeParams(params: readonly TypeParam[]): TypeParamInfo[] {
    const bounds = params.map((param) =>
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
    decl: DatatypeDecl,
  ): DatatypeInfo {
    return {
      name: mkDataName(decl.name.text),
      params: decl.typeParams.map(bindingHint),
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
 * types its patterns take apart cannot drift. `fields` are already closed over
 * the datatype's parameters, and they sit directly under this binder, so they
 * need no shifting.
 *
 * A constructor with no fields of a datatype with no parameters is a *value*:
 * there is nothing to apply and nothing to instantiate, so `True` rather than
 * `True()`. Both conditions are needed. `Nil` of `List[A]` still has a type
 * argument to fix, and `[A]List[A]` is a quantifier over a non-function --
 * which the value restriction rules out -- so it stays `[A]() -> List[A]` and
 * is written `Nil[Bool]()`.
 */
export function constructorType(
  datatype: DatatypeInfo,
  ctor: CtorInfo,
): Type {
  const result = TData(datatype.name, datatype.params.map((_, j) => BVar(j)));
  if (datatype.params.length === 0 && ctor.fields.length === 0) return result;
  return TFun(
    datatype.params.map((param) => mkTypeParamInfo(param, TUnknown)),
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
