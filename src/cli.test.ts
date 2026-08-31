/**
 * The CLI's search path. Everything else in `cli.ts` is I/O or argument
 * shuffling; what is worth pinning is where a spec is looked for and what a
 * resolved path is, since the walker keys include-once on the answer.
 */

import { expect } from "@std/expect";
import { includePathFileSystem, splitEntry } from "./cli.ts";

/** The real `stdlib/`, as an absolute path so the test does not read `cwd`. */
const STDLIB = new URL("../stdlib", import.meta.url).pathname;

Deno.test("cli: the entry's own directory leads the search path", () => {
  expect(splitEntry("stdlib/uses-data.ga")).toEqual({
    root: "stdlib",
    entry: "uses-data.ga",
  });
  // A bare filename resolves against the working directory, and `under` drops
  // the `.` so the resolved path is the spelling the reader typed.
  expect(splitEntry("uses-data.ga")).toEqual({
    root: ".",
    entry: "uses-data.ga",
  });
  expect(includePathFileSystem(["."]).resolve("deno.json")).toBe("deno.json");
});

Deno.test("cli: a spec is tried under each directory in turn", () => {
  const fs = includePathFileSystem([`${STDLIB}/rec`, STDLIB]);

  // Found in the second directory, and the path handed back is where it was
  // found rather than what was asked for.
  expect(fs.resolve("data/bool.ga")).toBe(`${STDLIB}/data/bool.ga`);
  expect(fs.read(`${STDLIB}/data/bool.ga`)).toContain("datatype Bool");

  // Named by nothing on the path.
  expect(fs.resolve("data/absent.ga")).toBeUndefined();

  // The plain-path rule is the filesystem's, not the search path's: no amount
  // of `-I` makes an escaping spec resolvable.
  expect(fs.resolve("../stdlib/data/bool.ga")).toBeUndefined();
});

Deno.test("cli: overlapping directories spell one file one way", () => {
  // Why the resolved host path is the key rather than the spec. Both spellings
  // name `rec/fix.ga`, so include-once sees one file -- keyed on the spec they
  // would be two, and `datatype Rec` would be declared twice.
  const fs = includePathFileSystem([STDLIB, `${STDLIB}/rec`]);
  expect(fs.resolve("rec/fix.ga")).toBe(`${STDLIB}/rec/fix.ga`);
  expect(fs.resolve("fix.ga")).toBe(`${STDLIB}/rec/fix.ga`);
});
