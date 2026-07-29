/**
 * The include walker: entry file in, splice order out.
 *
 * Inclusion is textual and flat. With no separate compilation a module is a run
 * of `let` bindings with no body, and including it splices those ahead of the
 * including file's own -- so a walk yields just an *order*.
 *
 * Bindings are sequential, so order is significant, so cycles are an error while
 * diamonds are not: post-order DFS gives an order exactly when the graph is
 * acyclic. The tri-colour marking below tells the two apart.
 *
 * Nothing here parses -- the walk must know the file set first.
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
import { stripComment } from "./lexer.ts";

/** `#include "path"` -- the whole directive must be its own line. */
const DIRECTIVE = /^#include[ ]+"([^"]*)"[ ]*$/;

export type Include = {
  readonly spec: string;
  readonly at: Position;
  readonly width: number;
};

/**
 * Read the directives at the top of a file. They must precede all other content:
 * C allows them anywhere, but with sequential bindings that would make a file's
 * meaning depend on where its includes sit.
 *
 * A `#` in column 1 is always a directive -- leading whitespace is significant
 * here, so no expression can start there.
 */
export function scanIncludes(source: Source): Result<readonly Include[]> {
  const includes: Include[] = [];
  const diagnostics: Diagnostic[] = [];
  let open = true;

  for (const [index, raw] of source.lines.entries()) {
    const at = mkPosition(source.id, index + 1, 1);
    // Comments are whitespace: one above the directives must not close the
    // section, one after a directive must not spoil the match.
    const line = stripComment(raw).trimEnd();
    if (!line.startsWith("#")) {
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

export type Loaded = {
  /** Every file read, indexed by `FileId`. */
  readonly sources: Sources;
  /** Post-order: concatenate in this order to get one program. */
  readonly order: readonly FileId[];
};

type Mark = "grey" | "black";

/**
 * Walk the include graph from `entry`, depth first. An unreadable file is still
 * registered, empty, so its `FileId` resolves and diagnostics can name a path.
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
    // A diamond: reached by another route and finished. Nothing to report.
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
      // Grey: a cycle. No order works, so skipping cannot resolve it.
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
