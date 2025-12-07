import { TypeNode, Tree, tySubst, mkRenamer, typeError, Pos } from "./defs";

type CtxEntry =
  | { kind: 'var'; t: TypeNode; }
  | { kind: 'tvar'; t: TypeNode; };


export class Typer
{
  ctx: Map<string, CtxEntry> = new Map();
  reps: Map<string, string[]> = new Map();

  private ctxPush(k: string, v: CtxEntry)
  {
    let kn = this.reps.get(k);
    if (kn && kn.length > 0)
    {
      let k1 = `${k}#${kn.length}`;
      kn.push(k1);
      this.ctx.set(k1, v);
      return mkRenamer(k, k1);
    }
    else
    {
      this.reps.set(k, [k]);
      this.ctx.set(k, v);
      return mkRenamer(k, k);
    }
  }

  private ctxPop(k: string)
  {
    let kn = this.reps.get(k)!;
    let k1 = kn.pop()!;
    this.ctx.delete(k1);
    if (!kn.length) this.reps.delete(k);
  }

  private ctxGet<K extends CtxEntry["kind"]>(name: string, pos: Pos, k: K)
  {
    let entry = this.ctx.get(name);
    if (!entry || entry.kind != k)
      throw typeError(pos, `unbound ${k} ${name}`);
    return entry as Extract<CtxEntry, { kind: K; }>;
  }

  private texpose<K extends TypeNode["kind"]>(t: Tree, k: K)
  {
    let ty = this.tinfer(t);
    while (ty.kind == "tvar")
    {
      let tmp = this.ctxGet(ty.name, ty.pos, "tvar");
      ty = tmp.t;
    }
    if (ty.kind != k)
      throw typeError(t.pos, `expect ${k}, got ${ty.kind}`);
    return ty as Extract<TypeNode, { kind: K; }>;
  }

  tinfer(t: Tree): TypeNode
  {
    if (t.kind == "num")
      return { kind: "prim", pos: t.pos, name: "Int" };

    else if (t.kind == "unit")
      return { kind: "prim", pos: t.pos, name: "Unit" };

    else if (t.kind == "id")
    {
      const entry = this.ctxGet(t.name, t.pos, "var");
      return entry.t;
    }

    else if (t.kind == "ref")
    {
      const argTy = this.tinfer(t.arg);
      return { kind: "ref", pos: t.pos, t: argTy };
    }

    else if (t.kind == "get")
    {
      const argTy = this.texpose(t.arg, "ref");
      return argTy.t;
    }

    else if (t.kind == "put")
    {
      const srcTy = this.tinfer(t.src);
      let dstTy = this.texpose(t.dst, "ref");
      this.subtype(srcTy, dstTy.t);
      this.subtype(dstTy.t, srcTy);
      return { kind: "prim", pos: t.pos, name: "Unit" };
    }

    else if (t.kind == "op")
    {
      for (const arg of t.args)
        this.tcheck(arg, { kind: "prim", name: "Int", pos: arg.pos });

      return { kind: "prim", pos: t.pos, name: "Int" };
    }

    else if (t.kind == "let")
    {
      const e1Ty = t.typ ?? this.tinfer(t.e1);
      if (t.typ) this.tcheck(t.e1, t.typ);
      const ren = this.ctxPush(t.name, { kind: "var", t: e1Ty });
      const e2Ty = this.tinfer(ren.treeRename(t.e2));
      this.ctxPop(t.name);
      return e2Ty;
    }

    else if (t.kind == "fun")
    {
      if (!t.typ) throw typeError(t.pos, "cannot infer without argument");
      const ren = this.ctxPush(t.arg, { kind: "var", t: t.typ });
      const bodyTy = this.tinfer(ren.treeRename(t.body));
      this.ctxPop(t.arg);
      return { kind: "fun", pos: t.pos, t1: t.typ, t2: bodyTy };
    }

    else if (t.kind == "app")
    {
      const funTy = this.texpose(t.fun, "fun");
      this.tcheck(t.arg, funTy.t1);
      return funTy.t2;
    }

    else if (t.kind == "tlet")
    {
      const ren = this.ctxPush(t.name, { kind: "tvar", t: t.e1 });
      const e2Ty = this.tinfer(ren.treeRename(t.e2));
      this.ctxPop(t.name);
      return tySubst(ren.dst, t.e1)(e2Ty);
    }

    else if (t.kind == "tfun")
    {
      if (!t.typ) throw typeError(t.pos, "cannot infer without argument");
      const ren = this.ctxPush(t.arg, { kind: "tvar", t: t.typ });
      const bodyTy = this.tinfer(ren.treeRename(t.body));
      this.ctxPop(t.arg);
      return { kind: "all", pos: t.pos, arg: t.arg, t1: t.typ, t2: bodyTy };
    }

    else if (t.kind == "tapp")
    {
      const funTy = this.texpose(t.fun, "all");
      this.subtype(t.typ, funTy.t1);
      return tySubst(funTy.arg, t.typ)(funTy.t2);
    }

    else return t;  // never
  }

  subtype(t1: TypeNode, t2: TypeNode): void
  {
    if (t2.kind == "any") return;

    else if (t1.kind == "prim" && t2.kind == "prim")
    {
      if (t1.name != t2.name)
        throw typeError(t1.pos, `unmatched prims ${t1.name} <: ${t2.name}`);
    }

    else if (t1.kind == "tvar")
    {
      if (t2.kind == "tvar")
      {
        if (t1.name != t2.name)
          throw typeError(t1.pos, `unmatched tvars ${t1.name} <: ${t2.name}`);
      }

      else
      {
        let entry = this.ctxGet(t1.name, t1.pos, "tvar");
        this.subtype(entry.t, t2);
      }
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

    else if (t1.kind == "all" && t2.kind == "all")
    {
      this.subtype(t2.t1, t1.t1);
      const ren1 = this.ctxPush(t1.arg, { kind: "tvar", t: t2.t1 });
      const ren2 = mkRenamer(t2.arg, ren1.dst);
      this.subtype(ren1.tyRename(t1.t2), ren2.tyRename(t2.t2));
      this.ctxPop(t1.arg);
    }

    else throw typeError(t1.pos, `unmatched kinds ${t1.kind} <: ${t2.kind}`);
  }

  tcheck(t: Tree, ty: TypeNode): void
  {
    if (t.kind == "ref" && ty.kind == "ref")
      this.tcheck(t.arg, ty.t);

    else if (t.kind == "fun" && ty.kind == "fun")
    {
      if (t.typ) this.subtype(ty.t1, t.typ);
      const ren = this.ctxPush(t.arg, { kind: "var", t: ty.t1 });
      this.tcheck(ren.treeRename(t.body), ty.t2);
      this.ctxPop(t.arg);
    }

    else if (t.kind == "tfun" && ty.kind == "all")
    {
      if (t.typ) this.subtype(ty.t1, t.typ);
      const ren = this.ctxPush(t.arg, { kind: "tvar", t: ty.t1 });
      const renTy = mkRenamer(ty.arg, ren.dst);
      this.tcheck(ren.treeRename(t.body), renTy.tyRename(ty.t2));
      this.ctxPop(t.arg);
    }

    else this.subtype(this.tinfer(t), ty);
  }
}