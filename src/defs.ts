export type Pos = [number, number];
export function syntaxError(pos: Pos, msg: string): Error
{
  return Error(`Syntax Error (${pos}): ${msg}`);
}
export function typeError(pos: Pos, msg: string): Error
{
  return Error(`Type Error (${pos}): ${msg}`);
}

export type TypeNode =
  | { kind: "any"; pos: Pos; }
  | { kind: "prim"; pos: Pos; name: string; }
  | { kind: "tvar"; pos: Pos; name: string; }
  | { kind: "ref"; pos: Pos; t: TypeNode; }
  | { kind: "fun"; pos: Pos; t1: TypeNode; t2: TypeNode; }
  | { kind: "all"; pos: Pos; arg: string; t1: TypeNode; t2: TypeNode; };

export type Tree =
  | { kind: "unit"; pos: Pos; }
  | { kind: "num"; pos: Pos; num: number; }
  | { kind: "id"; pos: Pos; name: string; }
  | { kind: "ref"; pos: Pos; arg: Tree; }
  | { kind: "get"; pos: Pos; arg: Tree; }
  | { kind: "put"; pos: Pos; dst: Tree; src: Tree; }
  | { kind: "op"; pos: Pos; op: string; args: Tree[]; }
  | { kind: "let"; pos: Pos; name: string; e1: Tree; e2: Tree; }
  | { kind: "fun"; pos: Pos; arg: string; typ?: TypeNode; body: Tree; }
  | { kind: "app"; pos: Pos; fun: Tree; arg: Tree; }
  | { kind: "tlet"; pos: Pos; name: string; e1: TypeNode; e2: Tree; }
  | { kind: "tfun"; pos: Pos; arg: string; typ?: TypeNode; body: Tree; }
  | { kind: "tapp"; pos: Pos; fun: Tree; typ: TypeNode; };


type Inspected =
  | number
  | string
  | Inspected[];

export function inspectType(t: TypeNode): Inspected
{
  if (t.kind == "any")
    return "Any";
  else if (t.kind == "prim")
    return t.name;
  else if (t.kind == "ref")
    return ["Ref", inspectType(t.t)];
  else if (t.kind == "fun")
    return ["(", inspectType(t.t1), ")->", inspectType(t.t2)];
  else if (t.kind == "tvar")
    return t.name;
  else if (t.kind == "all")
    return ["[", t.arg, "<:", inspectType(t.t1), "]->", inspectType(t.t2)];
  else
    return t;
}

export function inspectTree(t: Tree): Inspected
{
  if (t.kind == "id")
    return t.name;
  else if (t.kind == "unit")
    return "()";
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
  else if (t.kind == "op")
  {
    let args = t.args.map(inspectTree);
    return [t.op, ...args];
  }
  else return t;
}


export function tySubst(tvar: string, t1: TypeNode)
{
  return function subst(t: TypeNode): TypeNode
  {
    if (t.kind === "tvar" && t.name === tvar)
      return t1;

    else if (t.kind === "ref")
      return { ...t, t: subst(t.t) };

    else if (t.kind === "fun")
      return { ...t, t1: subst(t.t1), t2: subst(t.t2) };

    else if (t.kind === "all")
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
  tyRename = (t: TypeNode) => t;
  treeRename = (t: Tree) => t;
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

    else if (t.kind === "all")
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

export function mkRenamer(src: string, dst: string): IRenamer
{
  if (src == dst || src == "")
    return new DummyRenamer(dst);
  else
    return new Renamer(src, dst);
}