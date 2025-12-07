import { Pos, Tree, TypeNode } from "./defs";
import { Tokenizer, Token } from "./lexer";


const binops = new Map([
  ["+", 40], ["-", 40], ["*", 50], ["/", 50]
]);

function idName(id?: Token): string
{
  return (!id || id.text == "_") ? "" : id.text;
}


export class Parser extends Tokenizer
{
  async parseType(): Promise<TypeNode>
  {
    let peek: Token | undefined;
    if (peek = await this.tryGetToken(["Int", "Unit", "Any"]))
    {
      if (peek.text == "Any")
        return { kind: "any", pos: peek.pos };
      else
        return { kind: "prim", pos: peek.pos, name: peek.text };
    }

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
      let t1 = await this.parseType();
      await this.requireToken(")");
      await this.requireToken("->");
      let t2 = await this.parseType();
      return { kind: "fun", pos: peek.pos, t1, t2 };
    }

    else if (peek = await this.tryGetToken("["))
    {
      let arg = await this.requireToken({ cat: "id" });
      await this.requireToken("<:");
      let t1 = await this.parseType();
      await this.requireToken("]");
      await this.requireToken("->");
      let t2 = await this.parseType();
      return { kind: "all", pos: peek.pos, arg: arg.text, t1, t2 };
    }

    else return await this.unexpectedToken({ cat: "type start" });
  }

  async parseExp(prec: number): Promise<Tree>
  {
    let peek: Token | undefined;
    if (prec <= 0)
    {
      if (peek = await this.tryGetToken("let"))
      {
        let id = await this.requireToken({ cat: "id" });
        let typ: TypeNode | undefined;
        if (await this.tryGetToken(":"))
          typ = await this.parseType();
        await this.requireToken("=");
        let e1 = await this.parseExp(1);
        let e2: Tree;
        if (await this.parseLineSep(peek.pos))
          e2 = await this.parseExp(0);
        else
          e2 = { kind: "unit", pos: peek.pos };
        return { kind: "let", pos: peek.pos, name: idName(id), typ, e1, e2 };
      }

      else if (peek = await this.tryGetToken("type"))
      {
        let id = await this.requireToken({ cat: "id" });
        await this.requireToken("<:");
        let e1 = await this.parseType();
        let e2: Tree;
        if (await this.parseLineSep(peek.pos))
          e2 = await this.parseExp(0);
        else
          e2 = { kind: "unit", pos: peek.pos };
        return { kind: "tlet", pos: peek.pos, name: idName(id), e1, e2 };
      }

      else
      {
        peek = await this.peekToken();
        let e1 = await this.parseExp(1);
        if (await this.parseLineSep(peek.pos))
        {
          let e2 = await this.parseExp(0);
          return { kind: "let", pos: peek.pos, name: "", e1, e2 };
        }
        else return e1;
      }
    }

    else if (prec <= 10 && (peek = await this.tryGetToken("\\")))
    {
      let kind: "fun" | "tfun";
      let id: Token | undefined;
      let typ: TypeNode | undefined;

      if (await this.tryGetToken("("))
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

      else return await this.unexpectedToken({ cat: "fun arg" });

      let body = await this.parseExp(10);
      return { kind, pos: peek.pos, arg: idName(id), body, typ };
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
          let arg: Tree;
          if (await this.tryGetToken(")"))
            arg = { kind: "unit", pos: peek.pos };
          else
          {
            arg = await this.parseExp(1);
            await this.requireToken(")");
          }
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
          return await this.unexpectedToken({ cat: "uatom start" });

        else break;
      }

      return res;
    }
  }

  parse()
  {
    return this.parseExp(0);
  }

  private async parseLineSep(pos: Pos): Promise<boolean>
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