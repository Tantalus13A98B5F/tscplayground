/**
 * The type-declaration table: what a source type name may resolve to.
 *
 * Two namespaces, because they behave differently downstream. A datatype is
 * *nominal* -- `TData` carries its name and nothing unfolds it, so it may be
 * recursive. An alias is *transparent* -- it is expanded during elaboration and
 * nothing after this file knows it existed, so a recursive one would be an
 * infinite type.
 *
 * That asymmetry sets the build order. Datatype *signatures* (name and arity)
 * are collected in a first pass over every declaration, so a constructor field
 * may name its own datatype or one declared later; bodies are elaborated in a
 * second pass. Aliases stay strictly ordered against each other, which is what
 * rules their recursion out by construction rather than by a cycle check.
 *
 * Both `fields` and an alias `body` are stored *closed* over the declaration's
 * type parameters -- `BVar j` is parameter j -- so a use is an `openMany` and
 * a constructor's function type is derived rather than separately built.
 */

import type { Position } from "../diagnostics/diagnostic.ts";
import type { DataName, Type, Variance } from "./types.ts";

export type CtorInfo = {
  readonly name: string;
  /** Field types, closed over the owning datatype's parameters. */
  readonly fields: readonly Type[];
  readonly at: Position;
};

/**
 * One type parameter of a datatype: what it prints as, where it was written,
 * and how an argument filling it may move.
 *
 * A record and not a name, because the variance has to live somewhere and the
 * parameter is what it is about -- and because the site a phantom is reported
 * at is the parameter itself, not the declaration around it.
 *
 * `named` is false for a wildcard `_`, which is how an author says a parameter
 * is deliberately unused; nothing resolves to it and it is not reported as a
 * phantom.
 */
export type ParamInfo = {
  /** What diagnostics print. `_` for a wildcard. */
  readonly hint: string;
  readonly named: boolean;
  readonly at: Position;
  /**
   * Filled by `inferDatatypeVariance`, once, after every datatype's
   * constructors are in. Invariant until then, so a table read before the pass
   * has run concludes less rather than something unsound.
   */
  variance: Variance;
};

export type DatatypeInfo = {
  readonly name: DataName;
  /** Parameters, in order. Its length is the arity. */
  readonly params: readonly ParamInfo[];
  /**
   * Filled by the second pass, so these two are assignable where the rest of
   * the entry is fixed at declaration. The array itself is replaced, never
   * pushed to.
   */
  ctors: readonly CtorInfo[];
  /**
   * Whether `initCtors` has run. Not the same question as `ctors` being empty:
   * the two passes leave a signature standing with no constructors yet, and
   * this is what tells that apart from a datatype that turned out to have none.
   */
  initialized: boolean;
  readonly at: Position;
};

export type AliasInfo = {
  readonly name: string;
  /** Parameter names, in order. Its length is the arity. */
  readonly params: readonly string[];
  /** Right-hand side, closed over `params`. A use opens it. */
  readonly body: Type;
  readonly at: Position;
};

export class Declarations {
  readonly #datatypes = new Map<string, DatatypeInfo>();
  readonly #aliases = new Map<string, AliasInfo>();

  datatypeOf(name: string): DatatypeInfo | undefined {
    return this.#datatypes.get(name);
  }

  aliasOf(name: string): AliasInfo | undefined {
    return this.#aliases.get(name);
  }

  /** Every datatype, in declaration order. */
  datatypes(): readonly DatatypeInfo[] {
    return [...this.#datatypes.values()];
  }

  /**
   * How `name`'s `index`th argument may move -- the `ArgVariance` every walk
   * over a `TData` consults.
   *
   * Invariant where the table cannot answer: an undeclared name, an argument
   * past the arity, or a call made before the variance pass. Each of those is
   * either already reported or a checker asking less than it could, and
   * invariance is the reading that assumes nothing.
   */
  argVariance(name: string, index: number): Variance {
    return this.#datatypes.get(name)?.params[index]?.variance ?? 0;
  }

  /**
   * Where `name` was declared, and so whether it is taken at all. Datatypes and
   * aliases share the one namespace -- a use site cannot tell them apart, so
   * neither may shadow the other.
   */
  declaredAt(name: string): Position | undefined {
    return this.#datatypes.get(name)?.at ?? this.#aliases.get(name)?.at;
  }

  /**
   * Claim a name for a datatype signature, answering where it was already
   * declared if it was. Refused here rather than by the caller, so that "the
   * first declaration keeps the name" is a property of the table.
   */
  addDatatype(info: DatatypeInfo): Position | undefined {
    const previous = this.declaredAt(info.name);
    if (previous !== undefined) return previous;
    this.#datatypes.set(info.name, info);
    return undefined;
  }

  addAlias(info: AliasInfo): Position | undefined {
    const previous = this.declaredAt(info.name);
    if (previous !== undefined) return previous;
    this.#aliases.set(info.name, info);
    return undefined;
  }

  /**
   * Fill in a datatype's constructors, once. A second attempt is a second
   * declaration of the same name, whose signature was refused above; its
   * constructors are refused here for the same reason, so the datatype that
   * owns the name owns the constructors that came with it.
   */
  initCtors(name: string, ctors: readonly CtorInfo[]): boolean {
    const info = this.#datatypes.get(name);
    if (info === undefined || info.initialized) return false;
    info.ctors = ctors;
    info.initialized = true;
    return true;
  }

  /** The constructor `name` of datatype `owner`, or `undefined`. */
  ctorOf(owner: string, name: string): CtorInfo | undefined {
    return this.#datatypes.get(owner)?.ctors.find(
      (ctor) => ctor.name === name,
    );
  }
}
