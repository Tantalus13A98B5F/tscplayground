import { test, expect } from "vitest";
import { readFile, readString } from "./reader.js";
import { Tokenizer } from "./lexer.js";


async function linearTokens(stream: AsyncGenerator<string>)
{
  let tker = new Tokenizer(stream);
  let arr: string[] = [];
  while (true)
  {
    let tok = await tker.getToken();
    if (tok.cat == "eof") break;
    arr.push(tok.text);
  }
  return arr;
}


test("readFile", async () =>
{
  const result: string[] = [];
  for await (const lines of readFile("package.json"))
  {
    result.push(lines);
  }
  expect(result[1]?.trim()).toBe('"name": "tscground",');
});


test("tokenize", async () =>
{
  let src = readString(`
let f = { \\(x: Ref[Int])  # define a function
  x := !x + 1 }`);
  let tokens = await linearTokens(src);
  expect(tokens).toStrictEqual(["let", "f", "=", "{",
    "\\", "(", "x", ":", "Ref", "[", "Int", "]", ")",
    "x", ":=", "!", "x", "+", "1", "}"]);
});


test("wrong: number prefix", async () =>
{
  async function src()
  {
    await linearTokens(readString(`
123abc`));
  }
  await expect(src).rejects.toThrow();
});


test("wrong: key prefix", async () =>
{
  let toks = await linearTokens(readString(`
let123`));
  await expect(toks).toStrictEqual(["let123"]);
});