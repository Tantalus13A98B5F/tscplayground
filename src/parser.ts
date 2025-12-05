import { Tokenizer, Pos, Token } from "./lexer";

type TypeNode =
  | { kind: "prim"; pos: Pos; name: string; }
  | { kind: "tvar"; pos: Pos; name: string; }
  | { kind: "ref"; pos: Pos; t: TypeNode; }
  | { kind: "fun"; pos: Pos; argname: string; t1: TypeNode; t2: TypeNode; }
  | { kind: "tfun"; pos: Pos; argname: string; t1: TypeNode; t2: TypeNode; };

type Tree =
  | { kind: "num"; pos: Pos; num: number; }
  | { kind: "id"; pos: Pos; name: string; }
  | { kind: "ref"; pos: Pos; arg: Tree; }
  | { kind: "get"; pos: Pos; arg: Tree; }
  | { kind: "put"; pos: Pos; dst: Tree; src: Tree; }
  | { kind: "op"; pos: Pos; op: string; args: Tree[]; }
  | { kind: "let"; pos: Pos; name: string; e1: Tree; e2: Tree; }
  | { kind: "fun"; pos: Pos; arg: string; typ?: TypeNode; body: Tree; }
  | { kind: "app"; pos: Pos; fun: Tree; arg: Tree; }
  | { kind: "tfun"; pos: Pos; arg: string; typ?: TypeNode; body: Tree; }
  | { kind: "tapp"; pos: Pos; fun: Tree; typ: TypeNode; };


let binops = new Map([
  ["+", 40], ["-", 40], ["*", 50], ["/", 50]
]);


export class Parser extends Tokenizer
{
  async parseType(): Promise<TypeNode>
  {
    let peek: Token | undefined;
    if (peek = await this.tryGetToken(["Int", "Unit"]))
      return { kind: "prim", pos: peek.pos, name: peek.text };

    else if (peek = await this.tryGetToken("Ref"))
    {
      await this.requireToken("[");
      let typ = await this.parseType();
      await this.requireToken("]");
      return { kind: "ref", pos: peek.pos, t: typ };
    }

    else if (peek = await this.tryGetToken({ cat: "id" }))
      return { kind: "tvar", pos: peek.pos, name: peek.text };

    else if (peek = await this.tryGetToken("("))
    {
      let arg = await this.requireToken({ cat: "id" });
      await this.requireToken(":");
      let t1 = await this.parseType();
      await this.requireToken(")");
      await this.requireToken("->");
      let t2 = await this.parseType();
      return { kind: "fun", pos: peek.pos, argname: arg.text, t1, t2 };
    }

    else if (peek = await this.tryGetToken("["))
    {
      let arg = await this.requireToken({ cat: "id" });
      await this.requireToken("<:");
      let t1 = await this.parseType();
      await this.requireToken("]");
      await this.requireToken("->");
      let t2 = await this.parseType();
      return { kind: "tfun", pos: peek.pos, argname: arg.text, t1, t2 };
    }

    else
    {
      await this.requireToken({ cat: "type start", text: "id|([" });
      throw new Error();  // to keep the typer happy
    }
  }

  async parseExp(prec: number): Promise<Tree>
  {
    let peek: Token | undefined;
    if (prec <= 0)
    {
      if (peek = await this.tryGetToken("let"))
      {
        let id = await this.requireToken({ cat: "id" });
        await this.requireToken("=");
        let e1 = await this.parseExp(1);
        if (!(await this.parseLineSep(peek.pos)))
          await this.requireToken(";");
        let e2 = await this.parseExp(0);
        return { kind: "let", pos: peek.pos, name: id.text, e1, e2 };
      }

      peek = await this.peekToken();
      let e1 = await this.parseExp(1);
      if (await this.parseLineSep(peek.pos))
      {
        let e2 = await this.parseExp(0);
        return { kind: "let", pos: peek.pos, name: "", e1, e2 };
      }
      else return e1;
    }

    else if (prec <= 10 && (peek = await this.tryGetToken("\\")))
    {
      let kind: "fun" | "tfun";
      let id: Token | undefined;
      let typ: TypeNode | undefined;
      if (id = await this.tryGetToken({ cat: "id" }))
        kind = "fun";

      else if (await this.tryGetToken("("))
      {
        kind = "fun";
        if (id = await this.tryGetToken(")"))
        {
          typ = { kind: "prim", pos: id.pos, name: "Unit" };
          id = undefined;
        }
        else
        {
          id = await this.requireToken({ cat: "id" });
          if (await this.tryGetToken(":"))
            typ = await this.parseType();
          await this.requireToken(")");
        }
      }

      else if (await this.tryGetToken("["))
      {
        kind = "tfun";
        id = await this.requireToken({ cat: "id" });
        if (await this.tryGetToken("<:"))
          typ = await this.parseType();
        await this.requireToken("]");
      }

      else
      {
        await this.requireToken({ cat: "delim", text: "([" });
        throw new Error();  // only to keep the typer happy
      }

      let body = await this.parseExp(10);
      let arg = id ? id.text : "";
      if (typ)
        return { kind, pos: peek.pos, arg, body, typ };
      else
        return { kind, pos: peek.pos, arg, body };
    }

    else if (prec <= 30 && (peek = await this.tryGetToken("ref")))
    {
      let arg = await this.parseExp(31);
      return { kind: "ref", pos: peek.pos, arg };
    }

    else
    {
      let res = await this.parseUAtom();
      if (prec <= 20 && (peek = await this.tryGetToken(":=")))
      {
        let src = await this.parseExp(21);
        return { kind: "put", pos: peek.pos, dst: res, src };
      }

      let ops = binops.entries().filter(([_, p]) => prec <= p).map(([s]) => s).toArray();
      while (peek = await this.tryGetToken(ops))
      {
        let opprec = binops.get(peek.text)!;
        let rhs = await this.parseExp(opprec + 1);
        res = { kind: "op", pos: peek.pos, op: peek.text, args: [res, rhs] };
      }
      return res;
    }
  }

  async parseUAtom(): Promise<Tree>
  {
    let peek: Token | undefined;
    if (peek = await this.tryGetToken(["+", "-", "!"]))
    {
      let arg = await this.parseUAtom();
      if (peek.text == "!")
        return { kind: "get", pos: peek.pos, arg };
      else
        return { kind: "op", pos: peek.pos, op: peek.text, args: [arg] };
    }

    else if (peek = await this.tryGetToken({ cat: "num" }))
      return { kind: "num", pos: peek.pos, num: parseInt(peek.text) };

    else
    {
      let res: Tree | undefined;
      while (true)
      {
        if (res === undefined && (peek = await this.tryGetToken({ cat: "id" })))
          res = { kind: "id", pos: peek.pos, name: peek.text };

        else if (peek = await this.tryGetToken("("))
        {
          let arg = await this.parseExp(1);
          await this.requireToken(")");
          res = res ? { kind: "app", pos: peek.pos, fun: res, arg } : arg;
        }

        else if (peek = await this.tryGetToken("{"))
        {
          let arg = await this.parseExp(0);
          await this.requireToken("}");
          res = res ? { kind: "app", pos: peek.pos, fun: res, arg } : arg;
        }

        else if (res !== undefined && (peek = await this.tryGetToken("[")))
        {
          let typ = await this.parseType();
          await this.requireToken("]");
          res = { kind: "tapp", pos: peek.pos, fun: res, typ };
        }

        else if (res === undefined)
          await this.requireToken({ cat: "uatom start", text: "+-!id({" });

        else break;
      }

      return res;
    }
  }

  parse()
  {
    return this.parseExp(0);
  }

  async parseLineSep(pos: Pos): Promise<boolean>
  {
    let peek = await this.peekToken();
    if (peek.text == ";")
    {
      await this.getToken();
      return true;
    }
    if (peek.pos[0] > pos[0] && peek.text != "}" && peek.cat != "eof")
      return true;
    return false;
  }
}