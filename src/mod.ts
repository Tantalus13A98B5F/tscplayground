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
export type { DataName, Level, Type } from "./core/types.ts";
export type { Entry, TermBinding, TypeBinding } from "./core/context.ts";
export { Context } from "./core/context.ts";

import {
  type Diagnostic,
  failed,
  reportError,
  type Result,
  type Source,
  type Sources,
} from "./diagnostics/diagnostic.ts";
import { type Token, tokenize } from "./syntax/lexer.ts";
import { layout } from "./syntax/layout.ts";
import { loadSources, scanRequires } from "./syntax/require.ts";
import type { FileSystem } from "./io/files.ts";
import { parseProgram } from "./syntax/parser.ts";
import { checkProgram } from "./core/check.ts";
import { type Type, typeToString } from "./core/types.ts";

/**
 * Run the whole pipeline over one source file: tokenize, lay out, parse, check.
 *
 * Every phase runs to completion and every one reports, but only one of them
 * can end the run. The lexer skips a character it cannot read and layout closes
 * whatever the author left open, so neither has a failing path to branch on;
 * the parse is the first that can come back with nothing, and checking a tree
 * that failed to parse would bury the real error under consequences of it.
 *
 * Their `value` is asserted rather than handled. If either grows a way to fail,
 * that is a contract change we want to hear about, where handling it quietly
 * would pass an empty stream on and blame the program for the silence.
 *
 * There is no file system here, so a `#require` cannot be followed. The scan
 * still runs: the lexer skips directive lines on the assumption the walker read
 * them, and without this a required file would vanish without a word.
 */
export function checkSource(source: Source): Result<Type> {
  const diagnostics: Diagnostic[] = [];

  const required = scanRequires(source);
  diagnostics.push(...required.diagnostics);
  for (const directive of required.value ?? []) {
    diagnostics.push(
      reportError(
        `cannot require "${directive.spec}": this run has a single source`,
        directive.at,
        directive.width,
      ),
    );
  }

  const tokens = tokenize(source);
  diagnostics.push(...tokens.diagnostics);

  const laid = layout(tokens.value!);
  diagnostics.push(...laid.diagnostics);

  const program = parseProgram(laid.value!);
  diagnostics.push(...program.diagnostics);
  if (program.value === undefined) return failed(diagnostics);

  const checked = checkProgram(program.value);
  diagnostics.push(...checked.diagnostics);
  return { value: checked.type, diagnostics };
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

/**
 * Check a whole program: walk `#require` from `entry`, then lex, lay out, and
 * splice every file into one token stream before parsing it once.
 *
 * Requiring is textual and flat, so a required file contributes its bindings
 * ahead of the requiring file's own and the result is a single program -- which
 * is why this cannot parse each file separately: a module of bare `let`s is not
 * a program on its own, having no final expression.
 */
export function checkFiles(fileSystem: FileSystem, entry: string): Checked {
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
  if (end === undefined) return { ...failed<Type>(diagnostics), sources };
  // The entry file is last in post-order, so its `eof` ends the stream.
  tokens.push(end);

  const program = parseProgram(tokens);
  diagnostics.push(...program.diagnostics);
  if (program.value === undefined) {
    return { ...failed<Type>(diagnostics), sources };
  }

  const checked = checkProgram(program.value);
  return {
    value: checked.type,
    diagnostics: [...diagnostics, ...checked.diagnostics],
    sources,
  };
}

export { typeToString };
