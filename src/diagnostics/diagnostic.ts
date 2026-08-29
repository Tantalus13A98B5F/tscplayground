/**
 * Source text, positions, and diagnostics.
 *
 * Errors are *values*, not exceptions: every phase returns the diagnostics it
 * produced along with whatever partial result it managed.
 *
 * Two representation choices drive everything here:
 *
 *   - **Source is held as lines**, so a position is an index into that array and
 *     finding text to show costs one array access. It also makes the layout rule
 *     direct: indentation is the leading spaces of `lines[i]`. This rests on the
 *     invariant that **no token spans a line**, which holds because there are no
 *     string literals and no block comments.
 *   - **A position is a point, not a range.** An extent would have to be merged
 *     from children at every parser node construction, and the failure mode is
 *     silent -- a node keeps its first token's extent and the underline lies.
 *     Diagnostics wanting a wider caret carry `width` instead.
 */

/** Identifies a source file. Positions carry one so diagnostics can name it. */
export type FileId = number & { readonly __brand: "FileId" };

export const mkFileId = (n: number): FileId => n as FileId;

/**
 * A source file as its lines, terminators removed. CRLF is normalized here,
 * once, at the only boundary where it is a concern. A trailing newline yields a
 * final empty line -- where a cursor at end of file actually sits.
 */
export type Source = {
  readonly id: FileId;
  readonly path: string;
  readonly lines: readonly string[];
};

export function mkSource(
  text: string,
  path: string,
  id: FileId = mkFileId(0),
): Source {
  return { id, path, lines: text.split(/\r?\n/) };
}

/** The line `at` sits on, or `undefined` if the position is out of range. */
export function lineAt(source: Source, at: Position): string | undefined {
  return source.lines[at.line - 1];
}

/**
 * A point in a source file. `line` and `column` are **1-based** -- they exist
 * for humans and for the layout rule, and there is no 0-based sibling field to
 * confuse them with. `column` counts UTF-16 code units.
 */
export type Position = {
  readonly file: FileId;
  readonly line: number;
  readonly column: number;
};

export function mkPosition(
  file: FileId,
  line: number,
  column: number,
): Position {
  return { file, line, column };
}

/**
 * Where something no source file contains was written -- a builtin
 * declaration. Its file id is one no source can have, so nothing can print a
 * line for it; nothing points here, which is the property to keep.
 */
export const nowhere: Position = { file: mkFileId(-1), line: 0, column: 0 };

/** The very beginning of a file. */
export function startOf(file: FileId): Position {
  return { file, line: 1, column: 1 };
}

/**
 * Source order, for sorting diagnostics. Lexicographic on file, then line, then
 * column -- file first, or a run spanning several files would interleave.
 */
export function comparePositions(first: Position, second: Position): number {
  return first.file - second.file ||
    first.line - second.line ||
    first.column - second.column;
}

export type Severity = "error" | "warning" | "info";

export type Diagnostic = {
  readonly severity: Severity;
  readonly message: string;
  readonly at: Position;
  /**
   * How wide to draw the caret. A *rendering hint*, not an extent: nothing may
   * compute with it, and it is clipped to the line when drawn. Callers pass the
   * length of the token they are complaining about.
   */
  readonly width: number;
};

export function reportError(
  message: string,
  at: Position,
  width = 1,
): Diagnostic {
  return { severity: "error", message, at, width };
}

export function reportWarning(
  message: string,
  at: Position,
  width = 1,
): Diagnostic {
  return { severity: "warning", message, at, width };
}

/**
 * What a phase hands back.
 *
 * `diagnostics` are the authority on success, never `value`. A phase that
 * recovers in place hands back a value alongside errors -- the tokens that did
 * lex, the stream `layout` balanced -- so its presence claims only that
 * something structurally well-formed came out. Downstream must ask `hasErrors`
 * rather than read it as "no errors". The parser is stricter still, withholding
 * its tree the moment it reports anything.
 *
 * `value === undefined` is the narrower case of producing nothing at all, not
 * even a recovered husk, which usually means a phase could not start.
 *
 * Recovery makes continuing *safe*, but a driver may still decline to: running
 * a phase over a tree that already failed buries the real error under
 * consequences of it. Each phase runs to completion, and the driver decides.
 */
export type Result<T> = {
  readonly value: T | undefined;
  readonly diagnostics: readonly Diagnostic[];
};

/** A value came out. Says nothing about whether it is any good. */
export function produced<T>(
  value: T,
  diagnostics: readonly Diagnostic[] = [],
): Result<T> {
  return { value, diagnostics };
}

/** Nothing came out, not even a recovered value. */
export function failed<T>(diagnostics: readonly Diagnostic[]): Result<T> {
  return { value: undefined, diagnostics };
}

/** Whether to stop. Warnings alone must never hold a program back. */
export function hasErrors(diagnostics: readonly Diagnostic[]): boolean {
  return diagnostics.some((diagnostic) => diagnostic.severity === "error");
}

/**
 * Every file under consideration, indexed by `FileId`. Diagnostics carry a file
 * rather than a source because once requires are involved one run reports
 * against several files -- a redeclaration names two of them.
 */
export type Sources = readonly Source[];

export function sourceAt(
  sources: Sources,
  file: FileId,
): Source | undefined {
  return sources[file];
}

/** Render as `path:line:col: severity: message`. */
export function showDiagnostic(
  diagnostic: Diagnostic,
  sources: Sources,
): string {
  const { file, line, column } = diagnostic.at;
  const path = sourceAt(sources, file)?.path ?? "<unknown>";
  return `${path}:${line}:${column}: ${diagnostic.severity}: ${diagnostic.message}`;
}

/**
 * Render with the offending line and a caret ruler beneath it. The ruler is a
 * run of spaces then carets, which aligns only because tabs are rejected in the
 * source; with tabs a column would not be a printed cell and this would need a
 * width table.
 */
export function showDiagnosticWithLine(
  diagnostic: Diagnostic,
  sources: Sources,
): string {
  const head = showDiagnostic(diagnostic, sources);
  const source = sourceAt(sources, diagnostic.at.file);
  const text = source && lineAt(source, diagnostic.at);
  if (text === undefined) return head;

  const from = diagnostic.at.column - 1;
  const width = Math.max(1, Math.min(diagnostic.width, text.length - from));
  return `${head}\n${text}\n${" ".repeat(from)}${"^".repeat(width)}`;
}
