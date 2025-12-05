import { Parser } from "../src/parser";
import { readString } from "../src/reader";

test("first parser", async () =>
{
    let parser = new Parser(readString(`
1 + -2 * 3 + 5 * 6`));
    console.log(await parser.parse());
});

test("refs", async () =>
{
    let parser = new Parser(readString(`
let a = ref 1 + 2*3
a := -1 + !a`));
    console.log(await parser.parse());
});

test("fun", async () =>
{
    let parser = new Parser(readString(`
let f = \\(x) { x := !x + 1 }
f(ref 1 + 2 * 3)`));
    console.log(await parser.parse());
});