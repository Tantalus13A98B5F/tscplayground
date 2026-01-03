import { test, expect } from "vitest";
import { Parser } from "../src/parser.js";
import { readString } from "../src/reader.js";
import { inspectTree } from "../src/defs.js";



test("first parser", async () =>
{
  let parser = new Parser(readString(`
1 + -2 * 3 + 5 * 6`));
  expect(inspectTree(await parser.parse())).toStrictEqual(
    ["+", ["+", 1, ["*", ["-", 2], 3]], ["*", 5, 6]]
  );
});

test("refs", async () =>
{
  let parser = new Parser(readString(`
let a = ref 1 + 2*3
a := -1 + !a`));
  expect(inspectTree(await parser.parse())).toStrictEqual(
    ["let", "a", "", ["ref", ["+", 1, ["*", 2, 3]]],
      [":=", "a", ["+", ["-", 1], ["!", "a"]]]]
  );
});

test("fun", async () =>
{
  let parser = new Parser(readString(`
let f = \\(x) {
  let y = !x + 1
  x := y
}
f(ref 1 + 2 * 3)`));
  expect(inspectTree(await parser.parse())).toStrictEqual(
    ["let", "f", "",
      ["fun", "x", "",
        ["let", "y", "", ["+", ["!", "x"], 1],
          [":=", "x", "y"]]],
      ["@", "f", ["ref", ["+", 1, ["*", 2, 3]]]]]
  );
});

test("type binding", async () =>
{
  let parser = new Parser(readString(`
type T <: Any
let f = \\(x: Ref[T]) {
  let y = !x + 1
  x := y
}
f(ref 1 + 2 * 3)`));
  expect(inspectTree(await parser.parse())).toStrictEqual(
    ["type", "T", "Any",
      ["let", "f", "",
        ["fun", "x", ["Ref", "T"],
          ["let", "y", "", ["+", ["!", "x"], 1],
            [":=", "x", "y"]]],
        ["@", "f", ["ref", ["+", 1, ["*", 2, 3]]]]]]
  );
});