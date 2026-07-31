import { expect } from "@std/expect";
import {
  mkSource,
  showDiagnostic,
  type Sources,
} from "../diagnostics/diagnostic.ts";
import { isPlainPath, memoryFileSystem } from "../io/files.ts";
import { loadSources, scanIncludes } from "./include.ts";

/** The paths of a walk, in splice order. */
function spliced(sources: Sources, order: readonly number[]): string[] {
  return order.map((id) => sources[id]?.path ?? "<unknown>");
}

Deno.test("a plain path has no ., .., or empty segments", () => {
  expect(isPlainPath("lib/a.tg")).toBe(true);
  expect(isPlainPath("./a.tg")).toBe(false);
  expect(isPlainPath("../a.tg")).toBe(false);
  expect(isPlainPath("sub/../a.tg")).toBe(false);
  expect(isPlainPath("/a.tg")).toBe(false);
  expect(isPlainPath("a//b.tg")).toBe(false);
  expect(isPlainPath("")).toBe(false);
});

Deno.test("a non-plain spec resolves to nothing, even if the file exists", () => {
  // What forbidding `.` and `..` buys: one file has exactly one spelling.
  const files = memoryFileSystem({ "a.tg": "" });
  expect(files.resolve("a.tg")).toBe("a.tg");
  expect(files.resolve("./a.tg")).toBeUndefined();
  expect(files.resolve("sub/../a.tg")).toBeUndefined();
});

Deno.test("scanIncludes reads directives at the top of a file", () => {
  const source = mkSource('#include "a.tg"\n#include "b.tg"\nlet x = 1\n', "m");
  const scanned = scanIncludes(source);
  expect(scanned.diagnostics).toEqual([]);
  expect(scanned.value?.map((i) => i.spec)).toEqual(["a.tg", "b.tg"]);
});

Deno.test("a directive after other content is rejected", () => {
  const source = mkSource('let x = 1\n#include "a.tg"\n', "m.tg");
  const scanned = scanIncludes(source);
  expect(scanned.value).toEqual([]);
  expect(showDiagnostic(scanned.diagnostics[0]!, [source])).toBe(
    "m.tg:2:1: error: #include must come before any other content",
  );
});

Deno.test("blank lines do not close the directive section", () => {
  const source = mkSource('#include "a.tg"\n\n#include "b.tg"\n', "m");
  expect(scanIncludes(source).value?.length).toBe(2);
});

Deno.test("a comment above the directives does not close the section", () => {
  // If this counted as content, the directive below it would be rejected.
  const source = mkSource('// prelude\n#include "a.tg"\n', "m");
  const scanned = scanIncludes(source);
  expect(scanned.diagnostics).toEqual([]);
  expect(scanned.value?.map((i) => i.spec)).toEqual(["a.tg"]);
});

Deno.test("a directive may carry a trailing comment", () => {
  const source = mkSource('#include "a.tg" // why\n', "m");
  const scanned = scanIncludes(source);
  expect(scanned.diagnostics).toEqual([]);
  expect(scanned.value?.map((i) => i.spec)).toEqual(["a.tg"]);
});

Deno.test("a malformed directive is reported, not silently skipped", () => {
  const source = mkSource("#include a.tg\n", "m.tg");
  const scanned = scanIncludes(source);
  expect(showDiagnostic(scanned.diagnostics[0]!, [source])).toBe(
    'm.tg:1:1: error: malformed directive, expected #include "path"',
  );
});

Deno.test("includes are spliced before the including file", () => {
  const files = memoryFileSystem({
    "main.tg": '#include "lib/a.tg"\nlet main = 1\n',
    "lib/a.tg": "let a = 1\n",
  });
  const loaded = loadSources(files, "main.tg");
  expect(loaded.diagnostics).toEqual([]);
  expect(spliced(loaded.value!.sources, loaded.value!.order)).toEqual([
    "lib/a.tg",
    "main.tg",
  ]);
});

Deno.test("a diamond includes the shared file once, silently", () => {
  const files = memoryFileSystem({
    "main.tg": '#include "b.tg"\n#include "c.tg"\n',
    "b.tg": '#include "d.tg"\n',
    "c.tg": '#include "d.tg"\n',
    "d.tg": "let d = 1\n",
  });
  const loaded = loadSources(files, "main.tg");
  expect(loaded.diagnostics).toEqual([]);
  expect(spliced(loaded.value!.sources, loaded.value!.order)).toEqual([
    "d.tg",
    "b.tg",
    "c.tg",
    "main.tg",
  ]);
});

Deno.test("a cycle is an reportError, unlike a diamond", () => {
  // Both reach a file twice; only this one has no order to give.
  const files = memoryFileSystem({
    "a.tg": '#include "b.tg"\n',
    "b.tg": '#include "a.tg"\n',
  });
  const loaded = loadSources(files, "a.tg");
  expect(
    loaded.diagnostics.map((d) => showDiagnostic(d, loaded.value!.sources)),
  )
    .toEqual(["b.tg:1:1: error: circular include of a.tg"]);
});

Deno.test("a file including itself is a cycle", () => {
  const files = memoryFileSystem({ "a.tg": '#include "a.tg"\n' });
  const loaded = loadSources(files, "a.tg");
  expect(loaded.diagnostics.length).toBe(1);
  expect(spliced(loaded.value!.sources, loaded.value!.order)).toEqual(["a.tg"]);
});

Deno.test("a cycle still yields an order for the files it did reach", () => {
  // Recovery: the checker still gets a program.
  const files = memoryFileSystem({
    "a.tg": '#include "b.tg"\n',
    "b.tg": '#include "a.tg"\nlet b = 1\n',
  });
  const loaded = loadSources(files, "a.tg");
  expect(spliced(loaded.value!.sources, loaded.value!.order)).toEqual([
    "b.tg",
    "a.tg",
  ]);
});

Deno.test("an unresolvable include names the directive, not the file", () => {
  const files = memoryFileSystem({ "a.tg": '#include "gone.tg"\n' });
  const loaded = loadSources(files, "a.tg");
  expect(
    loaded.diagnostics.map((d) => showDiagnostic(d, loaded.value!.sources)),
  )
    .toEqual(['a.tg:1:1: error: cannot resolve "gone.tg"']);
});

Deno.test("a missing entry resolves to a named path, not <unknown>", () => {
  const loaded = loadSources(memoryFileSystem({}), "gone.tg");
  expect(loaded.value).toBeUndefined();
  expect(showDiagnostic(loaded.diagnostics[0]!, [mkSource("", "gone.tg")]))
    .toBe(
      "gone.tg:1:1: error: cannot resolve entry gone.tg",
    );
});
