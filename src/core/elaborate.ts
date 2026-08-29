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
  ParamInfo,
} from "./declarations.ts";
import {
  badUnder,
  BVar,
  closeFrom,
  FVar,
  mkDataName,
  mkTypeParamInfo,
  openMany,
  TData,
  TFun,
  TNever,
  TUnknown,
  type Type,
  type TypeParamInfo,
} from "./types.ts";
import { inferDatatypeVariance } from "./variance.ts";

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
