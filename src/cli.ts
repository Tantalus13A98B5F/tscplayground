/**
 * Command line driver: `deno task run [file]`, or piped stdin. One shot, not a
 * REPL -- if an interactive session appears later it should be its own task.
 * All Deno-specific I/O is confined to this file so `mod.ts` stays bundleable
 * for the browser.
 */

import { parseArgs } from "@std/cli/parse-args";
import {
  type Checked,
  checkFiles,
  checkSource,
  type FileSystem,
  isPlainPath,
  mkSource,
  showDiagnosticWithLine,
  typeToString,
} from "./mod.ts";

/**
 * The filesystem the require walker reads through, rooted at one directory.
 *
 * A root is what lets the walker keep plain paths. The entry may be written
 * however the shell likes, but everything it requires resolves against the
 * directory the entry sits in, so a spec means the same thing wherever written.
 */
function denoFileSystem(root: string): FileSystem {
  const full = (path: string) => `${root}/${path}`;
  return {
    resolve(spec) {
      if (!isPlainPath(spec)) return undefined;
      try {
        return Deno.statSync(full(spec)).isFile ? spec : undefined;
      } catch {
        return undefined;
      }
    },
    read(path) {
      try {
        return Deno.readTextFileSync(full(path));
      } catch {
        return undefined;
      }
    },
  };
}

/** Split a command-line path into the root to resolve against and the entry. */
function splitEntry(path: string): { root: string; entry: string } {
  const cut = path.lastIndexOf("/");
  return cut === -1
    ? { root: ".", entry: path }
    : { root: path.slice(0, cut), entry: path.slice(cut + 1) };
}

async function readStdin(): Promise<string> {
  const chunks: Uint8Array[] = [];
  for await (const chunk of Deno.stdin.readable) chunks.push(chunk);
  return new TextDecoder().decode(
    chunks.reduce(
      (all, chunk) => new Uint8Array([...all, ...chunk]),
      new Uint8Array(),
    ),
  );
}

/** Piped input cannot require anything -- there is no directory to resolve in. */
async function checkStdin(): Promise<Checked> {
  const source = mkSource(await readStdin(), "<stdin>");
  return { ...checkSource(source), sources: [source] };
}

async function main(): Promise<number> {
  const args = parseArgs(Deno.args);
  const path = args._[0]?.toString();

  let result: Checked;
  try {
    if (path === undefined) {
      result = await checkStdin();
    } else {
      const { root, entry } = splitEntry(path);
      result = checkFiles(denoFileSystem(root), entry);
    }
  } catch (thrown) {
    // A program error is a diagnostic, never an exception, so anything thrown
    // here is a checker bug -- a scope assertion, most likely. Report it
    // plainly rather than dumping a stack trace at whoever ran the CLI.
    console.error(thrown instanceof Error ? thrown.message : String(thrown));
    return 1;
  }

  for (const diagnostic of result.diagnostics) {
    console.error(showDiagnosticWithLine(diagnostic, result.sources));
  }
  if (result.value === undefined) return 1;

  console.log(typeToString(result.value));
  return 0;
}

if (import.meta.main) {
  Deno.exit(await main());
}
