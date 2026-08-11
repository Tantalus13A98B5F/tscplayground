import { expect } from "@std/expect";
import { checkFiles, memoryFileSystem, showDiagnostic } from "./mod.ts";
import { typeToString } from "./core/types.ts";

/** Check a file set, as a `[type, ...located messages]` tuple. */
function run(
  files: Record<string, string>,
  entry = "main.tg",
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
    "prelude.tg": PRELUDE,
    "main.tg": '#require "prelude.tg"\nid(True())\n',
  })).toEqual(["Bool"]);
});

Deno.test("a required file need not end in an expression", () => {
  // A module is a run of bindings with no body. It is not a program on its
  // own, which is why the splice happens before parsing rather than after.
  expect(run({
    "a.tg": "let x = True()",
    "b.tg": "datatype Bool where\n  | True\n  | False",
    "main.tg": '#require "b.tg"\n#require "a.tg"\nx\n',
  })).toEqual(["Bool"]);
});

Deno.test("a diagnostic names the file it came from, not the entry", () => {
  // What the token-level splice buys: every token keeps the FileId it was
  // lexed with, so a position still resolves to its own source.
  const [, ...messages] = run({
    "prelude.tg": PRELUDE + "\nlet broken = nope",
    "main.tg": '#require "prelude.tg"\nTrue()\n',
  });
  expect(messages).toEqual(["prelude.tg:5:14: error: unknown name nope"]);
});

Deno.test("requires are spliced in post-order, so a chain resolves", () => {
  expect(run({
    "base.tg": "datatype Bool where\n  | True\n  | False",
    "middle.tg": '#require "base.tg"\nlet t = True()',
    "main.tg": '#require "middle.tg"\nt\n',
  })).toEqual(["Bool"]);
});

Deno.test("a diamond contributes its shared file once", () => {
  // Twice would redeclare `Bool` and every constructor in it.
  expect(run({
    "base.tg": "datatype Bool where\n  | True\n  | False",
    "left.tg": '#require "base.tg"\nlet l = True()',
    "right.tg": '#require "base.tg"\nlet r = False()',
    "main.tg": '#require "left.tg"\n#require "right.tg"\nl\n',
  })).toEqual(["Bool"]);
});

Deno.test("a cycle is reported rather than looping", () => {
  const [, ...messages] = run({
    "a.tg": '#require "b.tg"\nlet x = y',
    "b.tg": '#require "a.tg"\nlet y = x',
    "main.tg": '#require "a.tg"\nx\n',
  });
  expect(messages.some((m) => m.includes("circular require"))).toBe(true);
});

Deno.test("an unresolvable require is reported at the directive", () => {
  const [, ...messages] = run({
    "main.tg": '#require "missing.tg"\nTrue()\n',
  });
  expect(messages[0]).toBe(
    'main.tg:1:1: error: cannot resolve "missing.tg"',
  );
});

Deno.test("a missing entry names the path it could not find", () => {
  const [type, ...messages] = run({}, "nowhere.tg");
  expect(type).toBe("<none>");
  expect(messages).toEqual([
    "nowhere.tg:1:1: error: cannot resolve entry nowhere.tg",
  ]);
});

Deno.test("a required file may declare a datatype the entry matches on", () => {
  expect(run({
    "prelude.tg": PRELUDE,
    "main.tg": [
      '#require "prelude.tg"',
      "match True() with",
      "  | True -> False()",
      "  | False -> True()",
    ].join("\n") + "\n",
  })).toEqual(["Bool"]);
});
