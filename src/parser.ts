import { Tokenizer } from "./lexer";

type TypeNode =
  | { kind: "prim"; name: string; }
  | { kind: "tvar"; name: string; }
  | { kind: "ref"; t: TypeNode; }
  | { kind: "fun"; argname: string; t1: TypeNode; t2: TypeNode; }
  | { kind: "tfun"; argname: string; t1: TypeNode; t2: TypeNode; };

type Tree =
  | { kind: "num"; num: number; }
  | { kind: "id"; name: string; }
  | { kind: "ref"; arg: Tree; }
  | { kind: "get"; arg: Tree; }
  | { kind: "put"; dst: Tree; src: Tree; }
  | { kind: "op"; op: string; args: Tree[]; }
  | { kind: "let"; name: string; e1: Tree; e2: Tree; }
  | { kind: "fun"; arg: string; typ?: TypeNode; body: Tree; }
  | { kind: "app"; fun: Tree; arg: Tree; }
  | { kind: "tfun"; arg: string; typ?: TypeNode; body: Tree; }
  | { kind: "tapp"; fun: Tree; typ: TypeNode; };


let binops = new Map([
  ["+", 40], ["-", 40], ["*", 50], ["/", 50]
]);


export class Parser extends Tokenizer
{
  async parseType(): Promise<TypeNode>
  {
    let peek = await this.peekToken();
    if (["Int", "Unit"].includes(peek.text))
    {
      await this.requireToken(peek);
      return { kind: "prim", name: peek.text };
    }

    if (peek.text == "Ref")
    {
      await this.requireToken(peek);
      await this.requireToken("[");
      let typ = await this.parseType();
      await this.requireToken("]");
      return { kind: "ref", t: typ };
    }

    if (peek.cat == "id")
    {
      await this.requireToken(peek);
      return { kind: "tvar", name: peek.text };
    }

    if (peek.text == "(")
    {
      await this.requireToken(peek);
      let arg = await this.requireToken({ cat: "id" });
      await this.requireToken(":");
      let t1 = await this.parseType();
      await this.requireToken(")");
      await this.requireToken("->");
      let t2 = await this.parseType();
      return { kind: "fun", argname: arg.text, t1, t2 };
    }

    if (peek.text == "[")
    {
      await this.requireToken(peek);
      let arg = await this.requireToken({ cat: "id" });
      await this.requireToken("<:");
      let t1 = await this.parseType();
      await this.requireToken("]");
      await this.requireToken("->");
      let t2 = await this.parseType();
      return { kind: "tfun", argname: arg.text, t1, t2 };
    }

    await this.requireToken({ cat: "type start", text: "id|([" });
    throw new Error();  // to keep the typer happy
  }

  async parseExp(prec: number): Promise<Tree>
  {
    let peek = await this.peekToken();
    if (prec <= 0)
    {
      if (peek.text == "let")
      {
        await this.requireToken(peek);
        let id = await this.requireToken({ cat: "id" });
        await this.requireToken("=");
        let e1 = await this.parseExp(1);
        await this.requireToken(";");
        let e2 = await this.parseExp(0);
        return { kind: "let", name: id.text, e1, e2 };
      }

      let e1 = await this.parseExp(1);
      peek = await this.peekToken();
      if (peek.text == ";")
      {
        await this.requireToken(peek);
        let e2 = await this.parseExp(0);
        return { kind: "let", name: "", e1, e2 };
      }
      else return e1;
    }

    if (prec <= 10 && peek.text == "\\")
    {
      await this.requireToken(peek);
      let argd = await this.peekToken();
      if (argd.text == "(")
      {
        await this.requireToken(argd);
        let id = await this.requireToken({ cat: "id" });
        let peek = await this.peekToken();
        let typ: TypeNode | undefined;
        if (peek.text == ":")
        {
          await this.requireToken(peek);
          typ = await this.parseType();
        }
        await this.requireToken(")");
        let body = await this.parseExp(10);
        let res: Tree = { kind: "fun", arg: id.text, body };
        return typ ? { ...res, typ } : res;
      }

      if (argd.text == "[")
      {
        await this.requireToken(argd);
        let id = await this.requireToken({ cat: "id" });
        let peek = await this.peekToken();
        let typ: TypeNode | undefined;
        if (peek.text == "<:")
        {
          await this.requireToken(peek);
          typ = await this.parseType();
        }
        await this.requireToken("]");
        let body = await this.parseExp(10);
        let res: Tree = { kind: "tfun", arg: id.text, body };
        return typ ? { ...res, typ } : res;
      }

      await this.requireToken({ cat: "delim", text: "([" });
      throw new Error();  // only to keep the typer happy
    }

    if (prec <= 30 && peek.text == "ref")
    {
      await this.requireToken(peek);
      let arg = await this.parseExp(31);
      return { kind: "ref", arg };
    }

    let res = await this.parseUAtom();
    peek = await this.peekToken();
    if (prec <= 20 && peek.text == ":=")
    {
      await this.requireToken(peek);
      let src = await this.parseExp(21);
      return { kind: "put", dst: res, src };
    }

    for (; binops.has(peek.text); peek = await this.peekToken())
    {
      let opprec = binops.get(peek.text)!;
      if (prec > opprec) break;
      await this.requireToken(peek);
      let rhs = await this.parseExp(opprec + 1);
      res = { kind: "op", op: peek.text, args: [res, rhs] };
    }
    return res;
  }

  async parseUAtom(): Promise<Tree>
  {
    let peek = await this.peekToken();
    if ("+-!".includes(peek.text))
    {
      await this.requireToken(peek);
      let arg = await this.parseUAtom();
      if (peek.text == "!")
        return { kind: "get", arg };
      else
        return { kind: "op", op: peek.text, args: [arg] };
    }

    if (peek.cat == "num")
    {
      await this.requireToken(peek);
      return { kind: "num", num: parseInt(peek.text) };
    }

    let res: Tree | undefined;
    while (true)
    {
      peek = await this.peekToken();
      if (res === undefined && peek.cat == "id")
      {
        await this.requireToken(peek);
        res = { kind: "id", name: peek.text };
      }

      else if (peek.text == "(")
      {
        await this.requireToken(peek);
        let arg = await this.parseExp(1);
        await this.requireToken(")");
        res = res ? { kind: "app", fun: res, arg } : arg;
      }

      else if (peek.text == "{")
      {
        await this.requireToken(peek);
        let arg = await this.parseExp(0);
        await this.requireToken("}");
        res = res ? { kind: "app", fun: res, arg } : arg;
      }

      else if (res !== undefined && peek.text == "[")
      {
        await this.requireToken(peek);
        let typ = await this.parseType();
        await this.requireToken("]");
        res = { kind: "tapp", fun: res, typ };
      }

      else if (res === undefined)
        await this.requireToken({ cat: "uatom start", text: "+-!id({" });

      else break;
    }

    return res;
  }

  parse()
  {
    return this.parseExp(0);
  }
}