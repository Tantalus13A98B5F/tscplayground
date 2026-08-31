/**
 * Command line driver: `deno task run [file] [-I dir]...`, or piped stdin. One
 * shot, not a REPL -- if an interactive session appears later it should be its
 * own task. All Deno-specific I/O is confined to this file so `mod.ts` stays
 * bundleable for the browser.
 */

import { parseArgs } from "@std/cli/parse-args";
import {
  type Checked,
  checkFiles,
  type FileSystem,
  isPlainPath,
  showDiagnosticWithLine,
  typeToString,
} from "./mod.ts";

/** Join a search directory to a spec, `.` contributing no prefix. */
function under(dir: string, spec: string): string {
  const trimmed = dir.replace(/\/+$/, "");
  return trimmed === "" || trimmed === "." ? spec : `${trimmed}/${spec}`;
}

/**
 * The filesystem the require walker reads through: a spec is tried under each
 * directory in turn and the first hit wins, which is `-I` in a C compiler.
 *
 * Search order does not weaken what `io/files.ts` says about plain paths. A
 * spec still means the same thing wherever written -- resolution reads the
 * search path and nothing about the requiring file, which is where C's `""`
 * form differs and why `resolve` still takes no `from`.
 *
 * A resolved path is the *host* path, so it is what include-once is keyed on.
 * That is the reason to prefer it to the spec: overlapping directories can
 * spell one file two ways -- `rec/fix.ga` under `stdlib` and `fix.ga` under
 * `stdlib/rec` -- and keying on where it was found makes those one file rather
 * than two copies of every binding it declares. It also gives a diagnostic a
 * path the reader can open, which the spec alone is not once there is more than
 * one place it could have come from.
 */
export function includePathFileSystem(dirs: readonly string[]): FileSystem {
  // Resolution stats; reading a second time would repeat the search.
  const found = new Map<string, string>();
  return {
    resolve(spec) {
      if (!isPlainPath(spec)) return undefined;
      const hit = found.get(spec);
      if (hit !== undefined) return hit;
      for (const dir of dirs) {
        const path = under(dir, spec);
        try {
          if (!Deno.statSync(path).isFile) continue;
        } catch {
          continue;
        }
        found.set(spec, path);
        return path;
      }
      return undefined;
    },
    read(path) {
      try {
        return Deno.readTextFileSync(path);
      } catch {
        return undefined;
      }
    },
  };
}

/**
 * Split a command-line path into the directory to search first and the entry.
 *
 * The entry's own directory leads the search path, so a lone file argument
 * behaves as it always did and `-I` is purely additive -- the same precedence a
 * C compiler gives the including file's directory.
 */
export function splitEntry(path: string): { root: string; entry: string } {
  const cut = path.lastIndexOf("/");
  return cut === -1
    ? { root: ".", entry: path }
    : { root: path.slice(0, cut), entry: path.slice(cut + 1) };
}

/**
 * Piped input with an entry of its own, so `-I` reaches a library from stdin.
 * The name is not a plain path away from being one a spec could collide with,
 * but it is `resolve`d like any other, which is what lets the walker start at
 * text that is on no disk.
 */
const STDIN = "<stdin>";

function stdinFileSystem(text: string, dirs: readonly string[]): FileSystem {
  const disk = includePathFileSystem(dirs);
  return {
    resolve(spec) {
      return spec === STDIN ? STDIN : disk.resolve(spec);
    },
    read(path) {
      return path === STDIN ? text : disk.read(path);
    },
  };
}

async function readStdin(): Promise<string> {
  // Decoded as it arrives: joining the chunks first would copy the whole input
  // once per chunk, and `stream` is what keeps a character split across a chunk
  // boundary intact.
  const decoder = new TextDecoder();
  let text = "";
  for await (const chunk of Deno.stdin.readable) {
    text += decoder.decode(chunk, { stream: true });
  }
  return text + decoder.decode();
}

/**
 * Every directory named by `-I` / `--include-dir`, in the order given. Repeated
 * rather than separator-joined: a path may contain the separator on some host,
 * and repetition is what a C compiler takes anyway.
 */
function includeDirs(values: readonly unknown[]): readonly string[] {
  return values.map(String).filter((dir) => dir !== "");
}

/**
 * A missing include directory is reported rather than skipped. A C compiler
 * ignores one, on the grounds that a search path is a set of guesses; here the
 * only reason to pass one is that a require needs it, so a typo would otherwise
 * surface as `cannot resolve` against a spec that is perfectly correct.
 */
function reportMissingDirs(dirs: readonly string[]): string[] {
  return dirs.filter((dir) => {
    try {
      return !Deno.statSync(dir).isDirectory;
    } catch {
      return true;
    }
  });
}

async function main(): Promise<number> {
  const args = parseArgs(Deno.args, {
    string: ["include-dir"],
    collect: ["include-dir"],
    alias: { "include-dir": "I" },
  });
  const path = args._[0]?.toString();
  const dirs = includeDirs(args["include-dir"]);

  for (const dir of reportMissingDirs(dirs)) {
    console.error(`no such include directory: ${dir}`);
    return 1;
  }

  let result: Checked;
  try {
    if (path === undefined) {
      // Stdin is an entry like any other now that `-I` can say where its
      // requires live; with no `-I` the search path is empty and a require in
      // piped text resolves to nothing, which is what it always did.
      result = checkFiles(stdinFileSystem(await readStdin(), dirs), STDIN);
    } else {
      const { root, entry } = splitEntry(path);
      result = checkFiles(includePathFileSystem([root, ...dirs]), entry);
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
