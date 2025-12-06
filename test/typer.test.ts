import { readString } from "../src/reader";
import { Parser } from "../src/parser";
import { Typer } from "../src/typer";

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