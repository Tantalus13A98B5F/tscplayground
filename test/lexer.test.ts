import { readFile, readString } from "../src/reader";
import { Tokenizer, Token } from "../src/lexer"


test("readFile", async () => {
  const result: string[] = [];
  for await (const lines of readFile("package.json")) {
    result.push(lines);
  }
  expect(result[1]?.trim()).toBe('"name": "tscground",');
});


test("tokenize", async () => {
  let src = readString(`
let f = fun (x: Ref[Int]) =>
  x := !x + 1`);
  let tker = new Tokenizer(src);
  let arr: Token[] = []
  while (true) {
    let tok = await tker.getToken();
    if (tok.cat == "eof") break;
    arr.push(tok)
  }
  console.log(arr)
})