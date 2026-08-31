/**
 * Public API. This is the entry point for both the CLI and the browser bundle,
 * so it must stay free of Deno-specific globals -- all I/O lives in `cli.ts`.
 */

export type {
  Diagnostic,
  FileId,
  Position,
  Result,
  Severity,
  Source,
} from "./diagnostics/diagnostic.ts";
export {
  mkSource,
  showDiagnostic,
  showDiagnosticWithLine,
} from "./diagnostics/diagnostic.ts";
export type { FileSystem } from "./io/files.ts";
export { isPlainPath, memoryFileSystem } from "./io/files.ts";
export type { Loaded, Require } from "./syntax/require.ts";
export { loadSources, scanRequires } from "./syntax/require.ts";
export type { TermNode, TypeNode } from "./syntax/ast.ts";
export type { Token, TokenKind } from "./syntax/lexer.ts";
export type { Level, Type } from "./core/types.ts";
export type {
  Binding,
  Entry,
  EVarEntry,
  TermVarEntry,
  TypeVarEntry,
} from "./core/context.ts";
export { Context } from "./core/context.ts";

import {
  type Diagnostic,
  failed,
  hasErrors,
  type Result,
  type Source,
  type Sources,
} from "./diagnostics/diagnostic.ts";
import { type Token, tokenize } from "./syntax/lexer.ts";
import { layout } from "./syntax/layout.ts";
import { loadSources } from "./syntax/require.ts";
import type { FileSystem } from "./io/files.ts";
import type { Program } from "./syntax/ast.ts";
import { parseProgram } from "./syntax/parser.ts";
import { checkProgram } from "./core/check.ts";
import { type Type, typeToString } from "./core/types.ts";
import { evaluate, type Value, valueToString } from "./core/evaluate.ts";

/**
 * A filesystem holding exactly `source`, under the path it already carries.
 *
 * Not `memoryFileSystem`, which resolves only *plain* paths -- a `Source`'s
 * path is a label a diagnostic prints, and `<stdin>` is one. This resolves the
 * entry whatever it is spelled, and nothing else, which is what a lone source
 * is: a filesystem of one file.
 *
 * The text is the lines rejoined, which is exact -- `mkSource` split them, and
 * splitting the join gives them back. Nothing else is reconstructed, so the
 * `Source` the walker registers is equal to the one handed in.
 */
function oneFileSystem(source: Source): FileSystem {
  const text = source.lines.join("\n");
  return {
    resolve: (spec) => spec === source.path ? spec : undefined,
    read: (path) => path === source.path ? text : undefined,
  };
}

/**
 * Run the whole pipeline over one source, with no filesystem behind it.
 *
 * A single source is a filesystem of one file, so this is `checkFiles` over
 * exactly that -- which is the whole implementation. Nothing about a lone
 * source differs from a walk that reads one file and finds no directives.
 *
 * `#require` is the case that looks like it needs its own handling and does
 * not. The walker resolves every directive against the filesystem it was
 * given; here that one refuses everything but the entry, so a directive is
 * reported as unresolvable, in the walker's words and at the walker's
 * position. Scanning for directives a second time to say something bespoke
 * about them is what this avoids -- and with it a second copy of the phase
 * sequence, which is where the two drifted apart before.
 */
export function checkSource(source: Source): Checked {
  return checkFiles(oneFileSystem(source), source.path);
}

/** `runFiles` over a lone source, as `checkSource` is `checkFiles` over one. */
export function runSource(source: Source): Ran {
  return runFiles(oneFileSystem(source), source.path);
}

/**
 * What a multi-file run hands back. `sources` comes along because diagnostics
 * carry a `FileId` rather than a path, and only the walk knows what was read.
 */
export type Checked = Result<Type> & { readonly sources: Sources };

/**
 * Append one file's tokens to the program being assembled.
 *
 * The splice is at the *token* level, not the text level. Laid-out streams
 * concatenate cleanly -- the layout rule opens no block around a whole file --
 * and every token keeps the `FileId` it was lexed with, so a diagnostic still
 * names the file it came from. Joining the sources as text would lose that.
 */
function appendPart(into: Token[], part: readonly Token[]): void {
  const body = part.filter((token) => token.kind !== "eof");
  if (body.length === 0) return;
  // Files are bindings in sequence, and a run of them wants the separator a
  // new line would have given. Marked `inserted`: no one wrote it.
  const last = into.at(-1);
  if (last !== undefined && last.kind !== "semi") {
    into.push({
      kind: "semi",
      text: ";",
      at: last.at,
      first: false,
      inserted: true,
    });
  }
  into.push(...body);
}

/** Everything up to a type: the tree, and what checking it came to. */
export function checkFiles(fileSystem: FileSystem, entry: string): Checked {
  const loaded = loadProgram(fileSystem, entry);
  if (loaded.value === undefined) {
    return { ...failed<Type>(loaded.diagnostics), sources: loaded.sources };
  }
  const checked = checkProgram(loaded.value);
  return {
    value: checked.type,
    diagnostics: [...loaded.diagnostics, ...checked.diagnostics],
    sources: loaded.sources,
  };
}

/**
 * What a run hands back: a type and a value, each absent where its phase had
 * nothing to give. Not a `Result` of a pair -- the phases are sequential and
 * fail separately, so a type that was inferred is worth having even where the
 * run it describes got stuck.
 */
export type Ran = {
  readonly type: Type | undefined;
  readonly value: Value | undefined;
  readonly diagnostics: readonly Diagnostic[];
  readonly sources: Sources;
};

/**
 * The whole pipeline: parse, check, evaluate, each contributing what it
 * reported.
 *
 * Evaluation is not gated on the check. It reads no types and is told nothing
 * about them, so a program that failed to check is one it can run and get stuck
 * in -- which is the only way to see what checking was buying, and is a thing
 * the tests do deliberately. What it is gated on is a tree, parsing being the
 * one phase that withholds its result.
 */
export function runFiles(fileSystem: FileSystem, entry: string): Ran {
  const loaded = loadProgram(fileSystem, entry);
  const { sources } = loaded;
  if (loaded.value === undefined) {
    return {
      type: undefined,
      value: undefined,
      diagnostics: loaded.diagnostics,
      sources,
    };
  }
  const checked = checkProgram(loaded.value);
  const ran = evaluate(loaded.value);
  return {
    type: checked.type,
    value: ran.value,
    diagnostics: [
      ...loaded.diagnostics,
      ...checked.diagnostics,
      ...ran.diagnostics,
    ],
    sources,
  };
}

/**
 * The tree every later phase reads: walk `#require` from `entry`, then lex, lay
 * out, and splice every file into one token stream before parsing it once.
 *
 * Requiring is textual and flat, so a required file contributes its bindings
 * ahead of the requiring file's own and the result is a single program -- which
 * is why this cannot parse each file separately: a module of bare `let`s is not
 * a program on its own, having no final expression.
 */
function loadProgram(
  fileSystem: FileSystem,
  entry: string,
): Result<Program> & { readonly sources: Sources } {
  // Asserted: the walk always hands back what it read, even for an entry it
  // could not resolve, because its diagnostics name files the caller can only
  // render through `sources`. An empty `order` is how it says it read nothing.
  const loaded = loadSources(fileSystem, entry);
  const { sources, order } = loaded.value!;

  const diagnostics: Diagnostic[] = [...loaded.diagnostics];
  const tokens: Token[] = [];
  let end: Token | undefined;

  for (const id of order) {
    const source = sources[id];
    if (source === undefined) continue;

    const lexed = tokenize(source);
    diagnostics.push(...lexed.diagnostics);

    // Asserted as in `checkSource`: every file contributes its tokens whatever
    // it reported, and the one parse below is where a multi-file run can stop.
    const laid = layout(lexed.value!);
    diagnostics.push(...laid.diagnostics);

    appendPart(tokens, laid.value!);
    end = laid.value!.at(-1);
  }

  // Nothing was read -- an unresolvable entry, already reported. Parsing an
  // empty stream would only add a confusing second error.
  if (end === undefined) return { ...failed<Program>(diagnostics), sources };
  // The entry file is last in post-order, so its `eof` ends the stream.
  tokens.push(end);

  const program = parseProgram(tokens);
  diagnostics.push(...program.diagnostics);
  return { ...program, diagnostics, sources };
}

export { evaluate, hasErrors, typeToString, valueToString };
export type { Value };
