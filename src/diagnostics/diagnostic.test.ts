import { expect } from "@std/expect";
import {
  comparePositions,
  failed,
  hasErrors,
  lineAt,
  mkFileId,
  mkPosition,
  mkSource,
  produced,
  reportError,
  reportWarning,
  showDiagnostic,
  showDiagnosticWithLine,
} from "./diagnostic.ts";

const source = mkSource("let x = 1\nlet y = zz\n", "demo.tg");
const file = source.id;

Deno.test("mkSource splits into lines and normalizes CRLF", () => {
  const crlf = mkSource("a\r\nb\r\n", "demo.tg");
  expect(crlf.lines).toEqual(["a", "b", ""]);
  expect(crlf.lines).toEqual(mkSource("a\nb\n", "demo.tg").lines);
});

Deno.test("a trailing newline leaves a final empty line", () => {
  // Where a cursor at the end of the file actually sits.
  expect(source.lines.length).toBe(3);
  expect(source.lines[2]).toBe("");
});

Deno.test("lineAt indexes directly, no scanning", () => {
  expect(lineAt(source, mkPosition(file, 2, 9))).toBe("let y = zz");
  expect(lineAt(source, mkPosition(file, 9, 1))).toBeUndefined();
});

Deno.test("showDiagnostic names the file, line and column", () => {
  expect(
    showDiagnostic(reportError("unbound variable", mkPosition(file, 2, 9)), [
      source,
    ]),
  )
    .toBe(
      "demo.tg:2:9: error: unbound variable",
    );
});

Deno.test("showDiagnosticWithLine underlines using the caret width", () => {
  const diagnostic = reportError("unbound variable", mkPosition(file, 2, 9), 2);
  expect(showDiagnosticWithLine(diagnostic, [source])).toBe(
    "demo.tg:2:9: error: unbound variable\nlet y = zz\n        ^^",
  );
});

Deno.test("a caret is at least one column wide", () => {
  const lines = showDiagnosticWithLine(
    reportError("boom", mkPosition(file, 1, 1), 0),
    [
      source,
    ],
  )
    .split("\n");
  expect(lines[2]).toBe("^");
});

Deno.test("a caret is clipped to the end of its line", () => {
  // A rendering hint, not an extent: an over-wide hint must not run off.
  const lines = showDiagnosticWithLine(
    reportError("boom", mkPosition(file, 1, 8), 99),
    [source],
  )
    .split("\n");
  expect(lines[1]).toBe("let x = 1");
  expect(lines[2]).toBe("       ^^");
});

Deno.test("showDiagnosticWithLine falls back to one line when out of range", () => {
  const diagnostic = reportError("boom", mkPosition(file, 99, 1));
  expect(showDiagnosticWithLine(diagnostic, [source])).toBe(
    showDiagnostic(diagnostic, [source]),
  );
});

Deno.test("comparePositions groups by file before line", () => {
  // Otherwise a run of diagnostics spanning several files interleaves them.
  const late = mkPosition(file, 9, 9);
  const other = mkPosition(mkFileId(1), 1, 1);
  expect(comparePositions(late, other)).toBeLessThan(0);
});

Deno.test("comparePositions orders by line, then column", () => {
  expect(comparePositions(mkPosition(file, 1, 9), mkPosition(file, 2, 1)))
    .toBeLessThan(0);
  expect(comparePositions(mkPosition(file, 2, 1), mkPosition(file, 2, 5)))
    .toBeLessThan(0);
  expect(comparePositions(mkPosition(file, 2, 5), mkPosition(file, 2, 5))).toBe(
    0,
  );
});

Deno.test("hasErrors ignores warnings, which must not hold a program back", () => {
  const at = mkPosition(file, 1, 1);
  expect(hasErrors([reportWarning("shadowed", at)])).toBe(false);
  expect(hasErrors([reportWarning("shadowed", at), reportError("boom", at)]))
    .toBe(true);
  expect(hasErrors([])).toBe(false);
});

Deno.test("a value may arrive alongside errors, since phases recover", () => {
  // `produced` claims only that something came out; diagnostics decide.
  const recovered = produced(["a"], [
    reportError("boom", mkPosition(file, 1, 1)),
  ]);
  expect(recovered.value).toEqual(["a"]);
  expect(hasErrors(recovered.diagnostics)).toBe(true);
  expect(failed<string[]>([]).value).toBeUndefined();
});
