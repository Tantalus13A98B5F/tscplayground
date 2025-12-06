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

interface IRenamer
{
  get dst(): string;
  tyRename(t: TypeNode): TypeNode;
  treeRename(t: Tree): Tree;
}

class DummyRenamer implements IRenamer
{
  constructor(readonly dst: string) { }

  tyRename(t: TypeNode): TypeNode
  {
    return t;
  }

  treeRename(t: Tree): Tree
  {
    return t;
  }
}

class Renamer implements IRenamer
{
  constructor(private src: string, readonly dst: string) { }

  tyRename(t: TypeNode): TypeNode
  {
    if (t.kind === "tvar" && t.name === this.src)
      return { ...t, name: this.dst };

    else if (t.kind === "ref")
      return { ...t, t: this.tyRename(t.t) };

    else if (t.kind === "fun")
      return { ...t, t1: this.tyRename(t.t1), t2: this.tyRename(t.t2) };

    else if (t.kind === "tfun")
    {
      let t2 = t.arg == this.src ? t.t2 : this.tyRename(t.t2);
      return { ...t, t1: this.tyRename(t.t1), t2 };
    }

    else return t;
  };

  treeRename(t: Tree): Tree
  {
    if (t.kind === "id" && t.name === this.src)
      return { ...t, name: this.dst };

    else if (t.kind === "ref")
      return { ...t, arg: this.treeRename(t.arg) };

    else if (t.kind === "get")
      return { ...t, arg: this.treeRename(t.arg) };

    else if (t.kind === "put")
      return { ...t, dst: this.treeRename(t.dst), src: this.treeRename(t.src) };

    else if (t.kind === "op")
      return { ...t, args: t.args.map(arg => this.treeRename(arg)) };

    else if (t.kind === "let")
    {
      let e2 = t.name === this.src ? t.e2 : this.treeRename(t.e2);
      return { ...t, e1: this.treeRename(t.e1), e2 };
    }

    else if (t.kind === "fun")
    {
      let typ = t.typ ? this.tyRename(t.typ) : undefined;
      let body = t.arg === this.src ? t.body : this.treeRename(t.body);
      return { ...t, typ, body };
    }

    else if (t.kind === "app")
      return { ...t, fun: this.treeRename(t.fun), arg: this.treeRename(t.arg) };

    else if (t.kind === "tlet")
    {
      let e2 = t.name === this.src ? t.e2 : this.treeRename(t.e2);
      return { ...t, e1: this.tyRename(t.e1), e2 };
    }

    else if (t.kind === "tfun")
    {
      let typ = t.typ ? this.tyRename(t.typ) : undefined;
      let body = t.arg === this.src ? t.body : this.treeRename(t.body);
      return { ...t, typ, body };
    }

    else if (t.kind === "tapp")
      return { ...t, fun: this.treeRename(t.fun), typ: this.tyRename(t.typ) };

    else
      return t;
  }
}

function deriveRenamer(ren: IRenamer, src: string)
{
  const dst = ren.dst;
  if (src == dst)
    return new DummyRenamer(dst);
  else
    return new Renamer(src, dst);
}


export class Typer
{
  ctx: Map<string, CtxEntry> = new Map();
  reps: Map<string, string[]> = new Map();

  private ctxPush(k: string, v: CtxEntry): IRenamer
  {
    let kn = this.reps.get(k);
    if (kn)
    {
      let k1 = `${k}#${kn.length}`;
      kn.push(k1);
      this.ctx.set(k1, v);
      return new Renamer(k, k1);
    }
    else
    {
      this.reps.set(k, [k]);
      this.ctx.set(k, v);
      return new DummyRenamer(k);
    }
  }

  private ctxPop(k: string)
  {
    let kn = this.reps.get(k)!;
    let k1 = kn.pop()!;
    this.ctx.delete(k1);
    if (!kn.length) this.reps.delete(k);
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
      const ren = this.ctxPush(t.name, { kind: "var", t: e1Ty });
      const e2Ty = this.tinfer(ren.treeRename(t.e2));
      this.ctxPop(t.name);
      return e2Ty;
    }

    else if (t.kind == "fun")
    {
      const argTy = t.typ!;
      const ren = this.ctxPush(t.arg, { kind: "var", t: argTy });
      const bodyTy = this.tinfer(ren.treeRename(t.body));
      this.ctxPop(t.arg);
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
      const ren = this.ctxPush(t.name, { kind: "tvar", t: t.e1 });
      const e2Ty = this.tinfer(ren.treeRename(t.e2));
      this.ctxPop(t.name);
      return e2Ty;
    }

    else if (t.kind == "tfun")
    {
      const typ = t.typ!;
      const ren = this.ctxPush(t.arg, { kind: "tvar", t: typ });
      const bodyTy = this.tinfer(ren.treeRename(t.body));
      this.ctxPop(t.arg);
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
    if (t2.kind == "prim" && t2.name == "Any") return;

    else if (t1 == t2) return;

    else if (t1.kind == "tvar")
    {
      let entry = this.ctx.get(t1.name);
      if (entry && entry.kind == "tvar")
        this.subtype(entry.t, t2);
      else
        throw new Error("t1 not a type");
    }

    else if (t1.kind == "ref" && t2.kind == "ref")
    {
      this.subtype(t1.t, t2.t);
      this.subtype(t2.t, t1.t);
    }

    else if (t1.kind == "fun" && t2.kind == "fun")
    {
      this.subtype(t2.t1, t1.t1);
      this.subtype(t1.t2, t2.t2);
    }

    else if (t1.kind == "tfun" && t2.kind == "tfun")
    {
      this.subtype(t2.t1, t1.t1);
      const ren1 = this.ctxPush(t1.arg, { kind: "tvar", t: t2.t1 });
      const ren2 = deriveRenamer(ren1, t2.arg);
      this.subtype(ren1.tyRename(t1.t2), ren2.tyRename(t2.t2));
      this.ctxPop(t1.arg);
    }

    else throw new Error("incomparable types");
  }

  tcheck(t: Tree, ty: TypeNode): void
  {
  }
}