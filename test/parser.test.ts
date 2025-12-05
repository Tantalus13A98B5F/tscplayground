import { Parser, Tree, TypeNode } from "../src/parser";
import { readString } from "../src/reader";


type Inspected =
  | number
  | string
  | Inspected[];

function inspectType(t: TypeNode): Inspected
{
  if (t.kind == "prim")
    return t.name;
  else if (t.kind == "ref")
    return ["Ref", inspectType(t.t)];
  else if (t.kind == "fun")
    return ["(", t.argname, inspectType(t.t1), ")->", inspectType(t.t2)];
  else if (t.kind == "tvar")
    return t.name;
  else //if (t.kind == "tfun")
    return ["[", t.argname, inspectType(t.t1), "]->", inspectType(t.t2)];
}

function inspectTree(t: Tree): Inspected
{
  if (t.kind == "id")
    return t.name;
  else if (t.kind == "num")
    return t.num;
  else if (t.kind == "ref")
    return ["ref", inspectTree(t.arg)];
  else if (t.kind == "get")
    return ["!", inspectTree(t.arg)];
  else if (t.kind == "put")
    return [":=", inspectTree(t.dst), inspectTree(t.src)];
  else if (t.kind == "app")
    return ["@", inspectTree(t.fun), inspectTree(t.arg)];
  else if (t.kind == "fun")
    return ["fun", t.arg, t.typ ? inspectType(t.typ) : "", inspectTree(t.body)];
  else if (t.kind == "tapp")
    return ["@", inspectTree(t.fun), inspectType(t.typ)];
  else if (t.kind == "tfun")
    return ["tfun", t.arg, t.typ ? inspectType(t.typ) : "", inspectTree(t.body)];
  else if (t.kind == "let")
    return ["let", t.name, inspectTree(t.e1), inspectTree(t.e2)];
  else if (t.kind == "tlet")
    return ["type", t.name, inspectType(t.e1), inspectTree(t.e2)];
  else //if (t.kind == "op")
  {
    let args = t.args.map(inspectTree);
    return [t.op, ...args];
  }
}


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
    ["let", "a", ["ref", ["+", 1, ["*", 2, 3]]],
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
    ["let", "f",
      ["fun", "x", "",
        ["let", "y", ["+", ["!", "x"], 1],
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
      ["let", "f",
        ["fun", "x", ["Ref", "T"],
          ["let", "y", ["+", ["!", "x"], 1],
            [":=", "x", "y"]]],
        ["@", "f", ["ref", ["+", 1, ["*", 2, 3]]]]]]
  );
});