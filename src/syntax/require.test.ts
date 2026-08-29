import { expect } from "@std/expect";
import {
  mkSource,
  showDiagnostic,
  type Sources,
} from "../diagnostics/diagnostic.ts";
import { isPlainPath, memoryFileSystem } from "../io/files.ts";
import { loadSources, scanRequires } from "./require.ts";

/** The paths of a walk, in splice order. */
function spliced(sources: Sources, order: readonly number[]): string[] {
  return order.map((id) => sources[id]?.path ?? "<unknown>");
}

Deno.test("a plain path has no ., .., or empty segments", () => {
  expect(isPlainPath("lib/a.ga")).toBe(true);
  expect(isPlainPath("./a.ga")).toBe(false);
  expect(isPlainPath("../a.ga")).toBe(false);
  expect(isPlainPath("sub/../a.ga")).toBe(false);
  expect(isPlainPath("/a.ga")).toBe(false);
  expect(isPlainPath("a//b.ga")).toBe(false);
  expect(isPlainPath("")).toBe(false);
});

Deno.test("a non-plain spec resolves to nothing, even if the file exists", () => {
  // What forbidding `.` and `..` buys: one file has exactly one spelling.
  const files = memoryFileSystem({ "a.ga": "" });
  expect(files.resolve("a.ga")).toBe("a.ga");
  expect(files.resolve("./a.ga")).toBeUndefined();
  expect(files.resolve("sub/../a.ga")).toBeUndefined();
});

Deno.test("scanRequires reads directives at the top of a file", () => {
  const source = mkSource('#require "a.ga"\n#require "b.ga"\nlet x = 1\n', "m");
  const scanned = scanRequires(source);
  expect(scanned.diagnostics).toEqual([]);
  expect(scanned.value?.map((i) => i.spec)).toEqual(["a.ga", "b.ga"]);
});

Deno.test("a directive after other content is rejected", () => {
  const source = mkSource('let x = 1\n#require "a.ga"\n', "m.ga");
  const scanned = scanRequires(source);
  expect(scanned.value).toEqual([]);
  expect(showDiagnostic(scanned.diagnostics[0]!, [source])).toBe(
    "m.ga:2:1: error: #require must come before any other content",
  );
});

Deno.test("blank lines do not close the directive section", () => {
  const source = mkSource('#require "a.ga"\n\n#require "b.ga"\n', "m");
  expect(scanRequires(source).value?.length).toBe(2);
});

Deno.test("a comment above the directives does not close the section", () => {
  // If this counted as content, the directive below it would be rejected.
  const source = mkSource('// prelude\n#require "a.ga"\n', "m");
  const scanned = scanRequires(source);
  expect(scanned.diagnostics).toEqual([]);
  expect(scanned.value?.map((i) => i.spec)).toEqual(["a.ga"]);
});

Deno.test("a directive may carry a trailing comment", () => {
  const source = mkSource('#require "a.ga" // why\n', "m");
  const scanned = scanRequires(source);
  expect(scanned.diagnostics).toEqual([]);
  expect(scanned.value?.map((i) => i.spec)).toEqual(["a.ga"]);
});

Deno.test("a malformed directive is reported, not silently skipped", () => {
  const source = mkSource("#require a.ga\n", "m.ga");
  const scanned = scanRequires(source);
  expect(showDiagnostic(scanned.diagnostics[0]!, [source])).toBe(
    'm.ga:1:1: error: malformed directive, expected #require "path"',
  );
});

Deno.test("requires are spliced before the requiring file", () => {
  const files = memoryFileSystem({
    "main.ga": '#require "lib/a.ga"\nlet main = 1\n',
    "lib/a.ga": "let a = 1\n",
  });
  const loaded = loadSources(files, "main.ga");
  expect(loaded.diagnostics).toEqual([]);
  expect(spliced(loaded.value!.sources, loaded.value!.order)).toEqual([
    "lib/a.ga",
    "main.ga",
  ]);
});

Deno.test("a diamond requires the shared file once, silently", () => {
  const files = memoryFileSystem({
    "main.ga": '#require "b.ga"\n#require "c.ga"\n',
    "b.ga": '#require "d.ga"\n',
    "c.ga": '#require "d.ga"\n',
    "d.ga": "let d = 1\n",
  });
  const loaded = loadSources(files, "main.ga");
  expect(loaded.diagnostics).toEqual([]);
  expect(spliced(loaded.value!.sources, loaded.value!.order)).toEqual([
    "d.ga",
    "b.ga",
    "c.ga",
    "main.ga",
  ]);
});

Deno.test("a cycle is an error, unlike a diamond", () => {
  // Both reach a file twice; only this one has no order to give.
  const files = memoryFileSystem({
    "a.ga": '#require "b.ga"\n',
    "b.ga": '#require "a.ga"\n',
  });
  const loaded = loadSources(files, "a.ga");
  expect(
    loaded.diagnostics.map((d) => showDiagnostic(d, loaded.value!.sources)),
  )
    .toEqual(["b.ga:1:1: error: circular require of a.ga"]);
});

Deno.test("a file requiring itself is a cycle", () => {
  const files = memoryFileSystem({ "a.ga": '#require "a.ga"\n' });
  const loaded = loadSources(files, "a.ga");
  expect(loaded.diagnostics.length).toBe(1);
  expect(spliced(loaded.value!.sources, loaded.value!.order)).toEqual(["a.ga"]);
});

Deno.test("a cycle still yields an order for the files it did reach", () => {
  // Recovery: the checker still gets a program.
  const files = memoryFileSystem({
    "a.ga": '#require "b.ga"\n',
    "b.ga": '#require "a.ga"\nlet b = 1\n',
  });
  const loaded = loadSources(files, "a.ga");
  expect(spliced(loaded.value!.sources, loaded.value!.order)).toEqual([
    "b.ga",
    "a.ga",
  ]);
});

Deno.test("an unresolvable require names the directive, not the file", () => {
  const files = memoryFileSystem({ "a.ga": '#require "gone.ga"\n' });
  const loaded = loadSources(files, "a.ga");
  expect(
    loaded.diagnostics.map((d) => showDiagnostic(d, loaded.value!.sources)),
  )
    .toEqual(['a.ga:1:1: error: cannot resolve "gone.ga"']);
});

Deno.test("a missing entry resolves to a named path, not <unknown>", () => {
  const loaded = loadSources(memoryFileSystem({}), "gone.ga");
  // The entry is registered even though it could not be read, and handed back
  // -- rendering the message needs the very sources the walk collected.
  expect(loaded.value?.order).toEqual([]);
  expect(showDiagnostic(loaded.diagnostics[0]!, loaded.value?.sources ?? []))
    .toBe("gone.ga:1:1: error: cannot resolve entry gone.ga");
});
