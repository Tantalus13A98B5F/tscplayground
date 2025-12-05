import { TypeNode, Tree } from "./parser";

type CtxEntry =
  | { kind: 'var'; t: TypeNode; }
  | { kind: 'tvar'; t: TypeNode; };

const arityMap = new Map([
  ["+", [1, 2]], ["-", [1, 2]], ["*", [2]], ["/", [2]]
]);


export class Typer
{
  ctx: Map<string, CtxEntry> = new Map();

  private get withEntry()
  {
    let self = this;
    return function* (k: string, v: CtxEntry): Generator<void>
    {
      let v0 = self.ctx.get(k);
      self.ctx.set(k, v);
      try
      {
        yield;
      }
      finally
      {
        if (v0)
          self.ctx.set(k, v0);
        else
          self.ctx.delete(k);
      }
    };
  }

  tinfer(t: Tree): TypeNode
  {
    if (t.kind == "num")
      return { kind: "prim", pos: t.pos, name: "Int" };

    else if (t.kind == "id")
    {
      const entry = this.ctx.get(t.name);
      if (!entry || entry.kind != "var")
        throw new Error(`Unbound variable: ${t.name}`);
      return entry.t;
    }

    else if (t.kind == "ref")
    {
      const argTy = this.tinfer(t.arg);
      return { kind: "ref", pos: t.pos, t: argTy };
    }

    else if (t.kind == "get")
    {
      const argTy = this.tinfer(t.arg);
      if (argTy.kind !== "ref")
        throw new Error("Cannot dereference non-ref type");
      return argTy.t;
    }

    else if (t.kind == "put")
    {
      const srcTy = this.tinfer(t.src);
      let dstTy = this.tinfer(t.dst);
      if (dstTy.kind !== "ref")
        throw new Error("Put destination must be a ref");
      dstTy = dstTy.t;
      this.subtype(srcTy, dstTy);
      this.subtype(dstTy, srcTy);
      return { kind: "prim", pos: t.pos, name: "Unit" };
    }

    else if (t.kind == "op")
    {
      if (!arityMap.get(t.op)!.includes(t.args.length))
        throw new Error("Wrong arity");
      for (const arg of t.args)
      {
        const argTy = this.tinfer(arg);
        if (argTy.kind !== "prim" || argTy.name !== "Int")
          throw new Error("Operator arguments must be Int");
      }
      return { kind: "prim", pos: t.pos, name: "Int" };
    }

    else if (t.kind == "let")
    {
      const e1Ty = this.tinfer(t.e1);
      for (let _ of this.withEntry(t.name, { kind: "var", t: e1Ty }))
        return this.tinfer(t.e2);
      throw new Error("unreachable");
    }

    else if (t.kind == "fun")
    {
      const argTy = t.typ!;
      let bodyTy: TypeNode;
      for (let _ of this.withEntry(t.arg, { kind: "var", t: argTy }))
        bodyTy = this.tinfer(t.body);
      return { kind: "fun", pos: t.pos, t1: argTy, t2: bodyTy! };
    }

    else if (t.kind == "app")
    {
      const funTy = this.tinfer(t.fun);
      const argTy = this.tinfer(t.arg);
      if (funTy.kind !== "fun")
        throw new Error("Trying to apply non-function");
      this.subtype(argTy, funTy.t1);
      return funTy.t2;
    }

    else if (t.kind == "tlet")
    {
      for (let _ of this.withEntry(t.name, { kind: "tvar", t: t.e1 }))
        return this.tinfer(t.e2);
      throw new Error("unreachable");
    }

    else if (t.kind == "tfun")
    {
      const typ = t.typ!;
      let bodyTy: TypeNode;
      for (let _ of this.withEntry(t.arg, { kind: "tvar", t: typ }))
        bodyTy = this.tinfer(t.body);
      return { kind: "tfun", pos: t.pos, arg: t.arg, t1: typ, t2: bodyTy! };
    }

    else //if (t.kind == "tapp")
    {
      const funTy = this.tinfer(t.fun);
      if (funTy.kind !== "tfun")
        throw new Error("Trying to type-apply non-type-function");
      this.subtype(t.typ, funTy.t1);
      return funTy.t2;
    }
  }

  subtype(t1: TypeNode, t2: TypeNode): void
  {
  }

  tcheck(t: Tree, ty: TypeNode): void
  {
  }
}