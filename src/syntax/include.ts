/**
 * The include walker: entry file in, ordered list of files out.
 *
 * Inclusion is textual and flat, in the spirit of `#include`. With no separate
 * compilation a module is not a unit with an interface -- it is a run of `let`
 * bindings with no body, and including it splices those bindings ahead of the
 * including file's own. A walk therefore yields just an *order*: concatenate the
 * files in it and you have one program.
 *
 *   - **Order is significant.** Bindings are sequential -- binding n sees
 *     bindings 1..n-1 and not the reverse.
 *   - **So cycles are an error and diamonds are not.** Post-order DFS gives a
 *     well-defined order exactly when the graph is acyclic. A diamond reaches a
 *     file by two routes and the second is skipped; a cycle has no order to
 *     give. The tri-colour marking distinguishes them exactly.
 *
 * Nothing here parses: directives are recognised lexically, since the walk must
 * know the file set before any file can be parsed as part of the whole.
 */

import {
  type Diagnostic,
  err,
  type FileId,
  mkFileId,
  mkPosition,
  mkSource,
  ok,
  type Position,
  reportError,
  type Result,
  type Source,
  type Sources,
} from "../diagnostics/diagnostic.ts";
import type { FileSystem } from "../io/files.ts";

/** `#include "path"` -- the whole directive must be its own line. */
const DIRECTIVE = /^#include[ ]+"([^"]*)"[ ]*$/;

export type Include = {
  readonly spec: string;
  readonly at: Position;
  readonly width: number;
};

/**
 * Read the directives at the top of a file.
 *
 * Directives must precede all other content. C allows them anywhere, but with
 * sequential bindings that would make a file's meaning depend on where its
 * includes sit; requiring them first makes splice order equal walk order.
 *
 * A `#` in column 1 is always a directive: leading whitespace is significant
 * here, so no expression can start there and be mistaken for one.
 */
export function scanIncludes(source: Source): Result<readonly Include[]> {
  const includes: Include[] = [];
  const diagnostics: Diagnostic[] = [];
  let open = true;

  for (const [index, line] of source.lines.entries()) {
    const at = mkPosition(source.id, index + 1, 1);
    if (!line.startsWith("#")) {
      // TODO: once line comments exist they must be skippable here too.
      if (line.trim() !== "") open = false;
      continue;
    }

    const matched = DIRECTIVE.exec(line);
    if (matched === null || matched[1] === undefined) {
      diagnostics.push(
        reportError(
          'malformed directive, expected #include "path"',
          at,
          line.length,
        ),
      );
      continue;
    }
    if (!open) {
      diagnostics.push(
        reportError(
          "#include must come before any other content",
          at,
          line.length,
        ),
      );
      continue;
    }
    includes.push({ spec: matched[1], at, width: line.length });
  }

  return ok(includes, diagnostics);
}

/** The outcome of a walk: what was read, and in what order to splice it. */
export type Loaded = {
  /** Every file read, indexed by `FileId`. */
  readonly sources: Sources;
  /** Post-order: concatenate the files in this order to get one program. */
  readonly order: readonly FileId[];
};

/** Where a file stands in the walk. See the tri-colour note above. */
type Mark = "grey" | "black";

/**
 * Walk the include graph from `entry`, depth first.
 *
 * A file that cannot be read is still registered, empty, so that its `FileId`
 * resolves and diagnostics against it can name a path rather than `<unknown>`.
 */
export function loadSources(
  fileSystem: FileSystem,
  entry: string,
): Result<Loaded> {
  const sources: Source[] = [];
  const ids = new Map<string, FileId>();
  const marks = new Map<string, Mark>();
  const order: FileId[] = [];
  const diagnostics: Diagnostic[] = [];

  const register = (path: string, text: string): Source => {
    const source = mkSource(text, path, mkFileId(sources.length));
    sources.push(source);
    ids.set(path, source.id);
    return source;
  };

  const walk = (path: string): void => {
    const mark = marks.get(path);
    // A diamond: already reached by another route and finished. Nothing to
    // report -- this is what include-once is for.
    if (mark === "black") return;
    marks.set(path, "grey");

    const text = fileSystem.read(path);
    const source = register(path, text ?? "");
    if (text === undefined) {
      diagnostics.push(
        reportError(`cannot read ${path}`, mkPosition(source.id, 1, 1)),
      );
      marks.set(path, "black");
      return;
    }

    const scanned = scanIncludes(source);
    diagnostics.push(...scanned.diagnostics);

    for (const include of scanned.value ?? []) {
      const resolved = fileSystem.resolve(include.spec);
      if (resolved === undefined) {
        diagnostics.push(
          reportError(
            `cannot resolve "${include.spec}"`,
            include.at,
            include.width,
          ),
        );
        continue;
      }
      // A grey hit is a cycle: no order puts its bindings before ours and
      // ours before its. Unlike a diamond, skipping cannot resolve it.
      if (marks.get(resolved) === "grey") {
        diagnostics.push(
          reportError(
            `circular include of ${resolved}`,
            include.at,
            include.width,
          ),
        );
        continue;
      }
      walk(resolved);
    }

    marks.set(path, "black");
    const id = ids.get(path);
    if (id !== undefined) order.push(id);
  };

  const start = fileSystem.resolve(entry);
  if (start === undefined) {
    const source = register(entry, "");
    return err([
      reportError(`cannot resolve entry ${entry}`, mkPosition(source.id, 1, 1)),
    ]);
  }
  walk(start);

  return { value: { sources, order }, diagnostics };
}
