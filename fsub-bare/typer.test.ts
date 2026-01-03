import { test, expect } from "vitest";
import { readString } from "./reader.js";
import { Parser } from "./parser.js";
import { Typer } from "./typer.js";

test("simple", async () =>
{
  let src = readString(`
let x = ref 1
let y = ref x
let inc = \\() !y := 1 + !!y
inc()
let double = \\(f: (Unit) -> Unit)
  { f(); f() }
double(inc)
!!y`);
  let parser = new Parser(src);
  let tree = await parser.parse();
  let typer = new Typer();
  typer.tinfer(tree);
});

test("flip", async () =>
{
  let src = readString(`
let x = ref 1
let y = ref x
let double = \\(f: (Unit) -> Unit)
  { f(); f() }
double(\\(x) !y := 1 + !!y)
!!y`);
  let parser = new Parser(src);
  let tree = await parser.parse();
  let typer = new Typer();
  typer.tinfer(tree);
});

test("type and var", async () =>
{
  let src = readString(`
type x <: Ref[Int]
!x
`);
  let parser = new Parser(src);
  let tree = await parser.parse();
  let typer = new Typer();
  expect(() => typer.tinfer(tree)).toThrow();
});

test("expose", async () =>
{
  let src = readString(`
1 := 1
`);
  let parser = new Parser(src);
  let tree = await parser.parse();
  let typer = new Typer();
  expect(() => typer.tinfer(tree)).toThrow();
});

test("pair", async () =>
{
  let src = readString(`
let mkPair = \\[A <: Any] \\[B <: Any] \\(a: A) \\(b: B)
  \\[C <: Any] \\(f: (A) -> (B) -> C) f(a)(b)
let p = mkPair[Int][Unit](1)()
let fst = \\[A <: Any] \\[B <: Any] \\(p: [C <: Any] -> ((A) -> (B) -> C) -> C)
  p[A](\\(x) \\(y) x)
let _: Int = fst[Int][Unit](p)
`);
  let parser = new Parser(src);
  let tree = await parser.parse();
  let typer = new Typer();
  typer.tinfer(tree);
});