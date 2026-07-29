/**
 * A read-only virtual filesystem.
 *
 * The include walker resolves and reads through this and nothing else, so the
 * same walker runs against a real directory under the CLI and against an
 * in-memory map in the browser, where there is no filesystem at all. That is why
 * this is the one contract in the project expressed as an `interface` rather
 * than a `type`: it exists to be implemented twice.
 *
 * Paths are **plain**: `/`-separated names from a single root, with no `.`, no
 * `..`, and no leading separator. This pays twice. Relative resolution
 * disappears, so a spec means the same thing wherever written; and so does
 * canonicalization, since a plain path is already canonical. Include-once is a
 * lookup keyed on that string, so two spellings of one file would give two
 * copies of every declaration -- forbidding the second is cheaper than
 * normalizing it.
 */

/** Is `path` a plain path? See the note above for why this is restrictive. */
export function isPlainPath(path: string): boolean {
  if (path === "") return false;
  return path.split("/").every((part) =>
    part !== "" && part !== "." && part !== ".."
  );
}

export interface FileSystem {
  /**
   * Resolve `spec` to a path this filesystem can read, or `undefined` if it
   * names nothing or is not a plain path.
   *
   * There is no `from` argument by design: paths are root-relative, so an
   * include spec does not depend on where it was written.
   */
  resolve(spec: string): string | undefined;

  /** Contents of a resolved path, or `undefined` if it cannot be read. */
  read(path: string): string | undefined;
}

/**
 * A filesystem backed by a map from path to contents. Used by the browser
 * bundle, by the playground, and by every test that involves more than one file.
 */
export function memoryFileSystem(files: Record<string, string>): FileSystem {
  const contents = new Map(Object.entries(files));
  return {
    resolve(spec) {
      return isPlainPath(spec) && contents.has(spec) ? spec : undefined;
    },
    read(path) {
      return contents.get(path);
    },
  };
}
