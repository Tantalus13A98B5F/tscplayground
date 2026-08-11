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
import type { DataName, Type } from "./types.ts";

export type CtorInfo = {
  readonly name: string;
  /** Field types, closed over the owning datatype's parameters. */
  readonly fields: readonly Type[];
  readonly at: Position;
};

export type DatatypeInfo = {
  readonly name: DataName;
  /** Parameter names, in order. Its length is the arity. */
  readonly params: readonly string[];
  readonly ctors: readonly CtorInfo[];
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
   * Is `name` taken in the type namespace? Datatypes and aliases share it --
   * a use site cannot tell them apart, so neither may shadow the other.
   */
  declares(name: string): boolean {
    return this.#datatypes.has(name) || this.#aliases.has(name);
  }

  /** Where `name` was declared, for a redeclaration diagnostic. */
  declaredAt(name: string): Position | undefined {
    return this.#datatypes.get(name)?.at ?? this.#aliases.get(name)?.at;
  }

  addDatatype(info: DatatypeInfo): void {
    this.#datatypes.set(info.name, info);
  }

  addAlias(info: AliasInfo): void {
    this.#aliases.set(info.name, info);
  }

  /** The constructor `name` of datatype `owner`, or `undefined`. */
  ctorOf(owner: string, name: string): CtorInfo | undefined {
    return this.#datatypes.get(owner)?.ctors.find(
      (ctor) => ctor.name === name,
    );
  }
}
