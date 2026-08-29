import { expect } from "@std/expect";
import { checkFiles, memoryFileSystem, showDiagnostic } from "./mod.ts";
import { typeToString } from "./core/types.ts";

/** Check a file set, as a `[type, ...located messages]` tuple. */
function run(
  files: Record<string, string>,
  entry = "main.ga",
): [string, ...string[]] {
  const result = checkFiles(memoryFileSystem(files), entry);
  return [
    result.value === undefined ? "<none>" : typeToString(result.value),
    ...result.diagnostics.map((d) => showDiagnostic(d, result.sources)),
  ];
}

const PRELUDE = [
  "datatype Bool where",
  "  | True",
  "  | False",
  "let id = fn [A](x: A) -> x",
].join("\n");

Deno.test("a required file's bindings are in scope in the requirer", () => {
  expect(run({
    "prelude.ga": PRELUDE,
    "main.ga": '#require "prelude.ga"\nid(True)\n',
  })).toEqual(["Bool"]);
});

Deno.test("a required file need not end in an expression", () => {
  // A module is a run of bindings with no body. It is not a program on its
  // own, which is why the splice happens before parsing rather than after.
  expect(run({
    "a.ga": "let x = True",
    "b.ga": "datatype Bool where\n  | True\n  | False",
    "main.ga": '#require "b.ga"\n#require "a.ga"\nx\n',
  })).toEqual(["Bool"]);
});

Deno.test("a diagnostic names the file it came from, not the entry", () => {
  // What the token-level splice buys: every token keeps the FileId it was
  // lexed with, so a position still resolves to its own source.
  const [, ...messages] = run({
    "prelude.ga": PRELUDE + "\nlet broken = nope",
    "main.ga": '#require "prelude.ga"\nTrue\n',
  });
  expect(messages).toEqual(["prelude.ga:5:14: error: unknown name nope"]);
});

Deno.test("requires are spliced in post-order, so a chain resolves", () => {
  expect(run({
    "base.ga": "datatype Bool where\n  | True\n  | False",
    "middle.ga": '#require "base.ga"\nlet t = True',
    "main.ga": '#require "middle.ga"\nt\n',
  })).toEqual(["Bool"]);
});

Deno.test("a diamond contributes its shared file once", () => {
  // Twice would redeclare `Bool` and every constructor in it.
  expect(run({
    "base.ga": "datatype Bool where\n  | True\n  | False",
    "left.ga": '#require "base.ga"\nlet l = True',
    "right.ga": '#require "base.ga"\nlet r = False',
    "main.ga": '#require "left.ga"\n#require "right.ga"\nl\n',
  })).toEqual(["Bool"]);
});

Deno.test("a cycle is reported rather than looping", () => {
  const [, ...messages] = run({
    "a.ga": '#require "b.ga"\nlet x = y',
    "b.ga": '#require "a.ga"\nlet y = x',
    "main.ga": '#require "a.ga"\nx\n',
  });
  expect(messages.some((m) => m.includes("circular require"))).toBe(true);
});

Deno.test("an unresolvable require is reported at the directive", () => {
  const [, ...messages] = run({
    "main.ga": '#require "missing.ga"\nTrue\n',
  });
  expect(messages[0]).toBe(
    'main.ga:1:1: error: cannot resolve "missing.ga"',
  );
});

Deno.test("a missing entry names the path it could not find", () => {
  const [type, ...messages] = run({}, "nowhere.ga");
  expect(type).toBe("<none>");
  expect(messages).toEqual([
    "nowhere.ga:1:1: error: cannot resolve entry nowhere.ga",
  ]);
});

Deno.test("a required file may declare a datatype the entry matches on", () => {
  expect(run({
    "prelude.ga": PRELUDE,
    "main.ga": [
      '#require "prelude.ga"',
      "match True with",
      "  | True -> False",
      "  | False -> True",
    ].join("\n") + "\n",
  })).toEqual(["Bool"]);
});
