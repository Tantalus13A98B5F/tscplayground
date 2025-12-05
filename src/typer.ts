import { TypeNode, Tree } from "./parser";

type CtxEntry =
  | { kind: 'var'; t: TypeNode; }
  | { kind: 'tvar'; t: TypeNode; };

const arityMap = new Map([
  ["+", [1, 2]], ["-", [1, 2]], ["*", [2]], ["/", [2]]
]);

function tySubst(tvar: string, t1: TypeNode)
{
  return function subst(t: TypeNode): TypeNode
  {
    if (t.kind === "tvar" && t.name === tvar)
      return t1;

    else if (t.kind === "ref")
      return { ...t, t: subst(t.t) };

    else if (t.kind === "fun")
      return { ...t, t1: subst(t.t1), t2: subst(t.t2) };

    else if (t.kind === "tfun")
    {
      if (t.arg === tvar)
        return t;
      else
        return {
          ...t,
          t1: subst(t.t1),
          t2: subst(t.t2)
        };
    }
    else return t;
  };
}


export class Typer
{
  ctx: Map<string, CtxEntry> = new Map();

  private withEntry<T>(k: string, v: CtxEntry, f: () => T): T
  {
    let v0 = this.ctx.get(k);
    this.ctx.set(k, v);
    try
    {
      return f();
    }
    finally
    {
      if (v0)
        this.ctx.set(k, v0);
      else
        this.ctx.delete(k);
    }
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
      return this.withEntry(t.name, { kind: "var", t: e1Ty },
        () => this.tinfer(t.e2));
    }

    else if (t.kind == "fun")
    {
      const argTy = t.typ!;
      const bodyTy = this.withEntry(t.arg, { kind: "var", t: argTy },
        () => this.tinfer(t.body));
      return { kind: "fun", pos: t.pos, t1: argTy, t2: bodyTy };
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
      return this.withEntry(t.name, { kind: "tvar", t: t.e1 },
        () => this.tinfer(t.e2));
    }

    else if (t.kind == "tfun")
    {
      const typ = t.typ!;
      const bodyTy = this.withEntry(t.arg, { kind: "tvar", t: typ },
        () => this.tinfer(t.body));
      return { kind: "tfun", pos: t.pos, arg: t.arg, t1: typ, t2: bodyTy };
    }

    else //if (t.kind == "tapp")
    {
      const funTy = this.tinfer(t.fun);
      if (funTy.kind !== "tfun")
        throw new Error("Trying to type-apply non-type-function");
      this.subtype(t.typ, funTy.t1);
      return tySubst(funTy.arg, t.typ)(funTy.t2);
    }
  }

  subtype(t1: TypeNode, t2: TypeNode): void
  {
  }

  tcheck(t: Tree, ty: TypeNode): void
  {
  }
}