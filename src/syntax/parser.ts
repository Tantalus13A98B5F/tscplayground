/**
 * Recursive descent over the token array, with layout resolved by `Cursor`.
 *
 * `parseProgram` is the only entry point that matters. The top level is a flat
 * *item* loop -- a declaration, a binding, or the final expression -- and the
 * bindings are folded into a `Let` chain at the end. So declarations are never
 * nested and never need lifting, and `parseExp` has no `data` case at all, which
 * is what makes "top-level only" hold by absence rather than by a check.
 *
 * Recovery returns `BadTerm`/`BadType` and carries on. Every loop either
 * consumes a token or breaks, so a malformed file cannot spin.
 */

import { ok, type Position, type Result } from "../diagnostics/diagnostic.ts";
import type {
  Arm,
  Bind,
  ConDecl,
  DataDecl,
  Field,
  Name,
  Param,
  Pattern,
  Program,
  Term,
  TypeBinder,
  TypeNode,
} from "./ast.ts";
import type { Token } from "./lexer.ts";
import { Cursor } from "./layout.ts";

/** `let` and sequencing: the forms that run to the end of their block. */
const BLOCK = 0;
/** An expression that stops before a `;` or a new line. */
const EXPR = 1;
/** `\` and `match`: greedy to the right, but nestable inside an argument. */
const PREFIX = 20;

export function parseProgram(tokens: readonly Token[]): Result<Program> {
  const parser = new Parser(tokens);
  const program = parser.program();
  return ok(program, parser.cursor.diagnostics);
}

/** Parse a single expression. For tests and the playground, not the pipeline. */
export function parseTerm(tokens: readonly Token[]): Result<Term> {
  const parser = new Parser(tokens);
  const term = parser.exp(BLOCK);
  return ok(term, parser.cursor.diagnostics);
}

export function parseType(tokens: readonly Token[]): Result<TypeNode> {
  const parser = new Parser(tokens);
  const type = parser.type();
  return ok(type, parser.cursor.diagnostics);
}

class Parser {
  readonly cursor: Cursor;

  constructor(tokens: readonly Token[]) {
    this.cursor = new Cursor(tokens);
  }

  program(): Program {
    const at = this.cursor.here;
    const decls: DataDecl[] = [];
    const binds: Bind[] = [];
    let body: Term | undefined;

    while (!this.cursor.isEof) {
      const mark = this.cursor.mark();

      if (this.cursor.at("data")) {
        const decl = this.dataDecl();
        if (decl !== undefined) decls.push(decl);
      } else if (this.cursor.at("let")) {
        const head = this.letHead();
        binds.push({ ...head, at: head.bound.at });
      } else {
        const at = this.cursor.here;
        const term = this.exp(EXPR);
        // Only the last item is the result; anything before it is sequencing.
        if (this.cursor.isEof) {
          body = term;
          break;
        }
        binds.push({ name: wildcard(at), bound: term, at });
      }

      if (this.cursor.isEof) break;
      if (!this.cursor.tryStartNextLine()) {
        this.cursor.report("`;` or a new line, then the rest of the program");
        this.cursor.skipToBlockStart();
      }
      if (this.cursor.mark() === mark) this.cursor.advance(); // ensure progress
    }

    if (body === undefined) {
      this.cursor.report("an expression to be the program's result");
      body = { kind: "BadTerm", at: this.cursor.here };
    }

    const term = binds.reduceRight<Term>(
      (rest, bind) => ({
        kind: "Let",
        name: bind.name,
        ...(bind.annotation === undefined
          ? {}
          : { annotation: bind.annotation }),
        bound: bind.bound,
        body: rest,
        at: bind.at,
      }),
      body,
    );
    return { decls, term, at };
  }

  /** `data Pair[A, B]` then its constructor arms. */
  private dataDecl(): DataDecl | undefined {
    const keyword = this.cursor.accept("data");
    if (keyword === undefined) return undefined;
    const name = this.name("a type name");
    if (name === undefined) return undefined;

    const params: Name[] = [];
    if (this.cursor.accept("lbracket") !== undefined) {
      do {
        const param = this.name("a type parameter");
        if (param === undefined) break;
        params.push(param);
      } while (this.cursor.accept("comma") !== undefined);
      this.cursor.expect("rbracket", "`]`");
    }

    const constructors = this.arms("a constructor", () => this.conDecl());
    return { name, params, constructors, at: keyword.at };
  }

  private conDecl(): ConDecl | undefined {
    const bar = this.cursor.accept("bar");
    if (bar === undefined) return undefined;
    const name = this.name("a constructor name");
    if (name === undefined) return undefined;

    const fields: Field[] = [];
    if (this.cursor.accept("lparen") !== undefined) {
      if (!this.cursor.at("rparen")) {
        do {
          const field = this.field();
          if (field === undefined) break;
          fields.push(field);
        } while (this.cursor.accept("comma") !== undefined);
      }
      this.cursor.expect("rparen", "`)`");
    }
    return { name, fields, at: bar.at };
  }

  private field(): Field | undefined {
    const name = this.name("a field name");
    if (name === undefined) return undefined;
    // Required: a field has nothing to infer an annotation from.
    this.cursor.expect("colon", "`:`, since every field is annotated");
    return { name, annotation: this.type(), at: name.at };
  }

  /**
   * A run of `|` arms, forming a block at the first one's column. The marker is
   * what allows the block to start at the enclosing column: without it, an arm
   * there would be indistinguishable from whatever follows the construct.
   */
  private arms<T>(what: string, parse: () => T | undefined): T[] {
    const results: T[] = [];
    this.cursor.block(false, () => {
      while (this.cursor.at("bar")) {
        const mark = this.cursor.mark();
        const parsed = parse();
        if (parsed !== undefined) results.push(parsed);
        if (this.cursor.mark() === mark) break;
        this.cursor.tryStartNextLine();
      }
    });
    if (results.length === 0) this.cursor.report(`at least one ${what}`);
    return results;
  }

  private letHead(): { name: Name; annotation?: TypeNode; bound: Term } {
    const keyword = this.cursor.accept("let");
    const at = keyword?.at ?? this.cursor.here;
    const name = this.name("a name to bind") ?? wildcard(at);
    const annotation = this.cursor.accept("colon") === undefined
      ? undefined
      : this.type();
    this.cursor.expect("equals", "`=`");
    const bound = this.blockOrExp(EXPR);
    return annotation === undefined
      ? { name, bound }
      : { name, annotation, bound };
  }

  /**
   * A newline here opens an indented block; otherwise the expression continues
   * on this line. One function, and the only place blocks are introduced.
   */
  private blockOrExp(prec: number): Term {
    if (!this.cursor.raw.first) return this.exp(prec);
    const at = this.cursor.here;
    return this.cursor.block(true, () => this.exp(BLOCK)) ??
      { kind: "BadTerm", at };
  }

  exp(prec: number): Term {
    if (prec <= BLOCK && this.cursor.at("let")) {
      const at = this.cursor.here;
      const head = this.letHead();
      if (!this.cursor.tryStartNextLine()) {
        this.cursor.report("`;` or a new line, then the body");
      }
      return { kind: "Let", ...head, body: this.exp(BLOCK), at };
    }

    if (prec <= PREFIX && this.cursor.at("lambda")) return this.abs();
    if (prec <= PREFIX && this.cursor.at("match")) return this.match();

    if (prec <= BLOCK) {
      // `e1; e2` binds nothing, but keeps its place once effects exist.
      const at = this.cursor.here;
      const first = this.exp(EXPR);
      if (!this.cursor.tryStartNextLine()) return first;
      return {
        kind: "Let",
        name: wildcard(at),
        bound: first,
        body: this.exp(BLOCK),
        at,
      };
    }

    return this.app();
  }

  /** `\(x: A) e`, or `\[T <: A](x: T) e` -- one binder, both worlds. */
  private abs(): Term {
    const at = this.cursor.here;
    this.cursor.advance();
    const tyParams = this.cursor.at("lbracket") ? this.typeBinders() : [];
    const params: Param[] = [];
    if (this.cursor.expect("lparen", "`(`, a parameter list") !== undefined) {
      if (!this.cursor.at("rparen")) {
        do {
          const name = this.name("a parameter name");
          if (name === undefined) break;
          const annotation = this.cursor.accept("colon") === undefined
            ? undefined
            : this.type();
          params.push(
            annotation === undefined
              ? { name, at: name.at }
              : { name, annotation, at: name.at },
          );
        } while (this.cursor.accept("comma") !== undefined);
      }
      this.cursor.expect("rparen", "`)`");
    }
    return { kind: "Abs", tyParams, params, body: this.blockOrExp(EXPR), at };
  }

  private match(): Term {
    const at = this.cursor.here;
    this.cursor.advance();
    const scrutinee = this.exp(PREFIX + 1);
    const arms = this.arms("arm", () => this.arm());
    return { kind: "Match", scrutinee, arms, at };
  }

  private arm(): Arm | undefined {
    const bar = this.cursor.accept("bar");
    if (bar === undefined) return undefined;
    const pattern = this.pattern();
    this.cursor.expect("fatArrow", "`=>`");
    return { pattern, body: this.blockOrExp(EXPR), at: bar.at };
  }

  /**
   * `_`, `C`, or `C(x, y)`. A name in this position is always a constructor and
   * a name inside the parentheses is always a binder, so a misspelt constructor
   * cannot quietly become a catch-all.
   */
  private pattern(): Pattern {
    const wild = this.cursor.accept("wild");
    if (wild !== undefined) return { kind: "PWild", at: wild.at };

    const name = this.name("a constructor name or `_`");
    if (name === undefined) return { kind: "PWild", at: this.cursor.here };

    const args: Name[] = [];
    if (this.cursor.accept("lparen") !== undefined) {
      if (!this.cursor.at("rparen")) {
        do {
          const arg = this.cursor.accept("wild");
          if (arg !== undefined) {
            args.push({ text: "_", at: arg.at });
            continue;
          }
          const bound = this.name("a name to bind");
          if (bound === undefined) break;
          args.push(bound);
        } while (this.cursor.accept("comma") !== undefined);
      }
      this.cursor.expect("rparen", "`)`");
    }
    return { kind: "PCon", name, args, at: name.at };
  }

  /** Application and instantiation, both postfix and both left-associative. */
  private app(): Term {
    let term = this.atom();
    for (;;) {
      const open = this.cursor.peek();
      if (open?.kind === "lparen") {
        this.cursor.advance();
        const args: Term[] = [];
        if (!this.cursor.at("rparen")) {
          do args.push(this.exp(EXPR)); while (
            this.cursor.accept("comma") !== undefined
          );
        }
        this.cursor.expect("rparen", "`)`");
        term = { kind: "App", callee: term, args, at: open.at };
      } else if (open?.kind === "lbracket") {
        this.cursor.advance();
        const args: TypeNode[] = [];
        do args.push(this.type()); while (
          this.cursor.accept("comma") !== undefined
        );
        this.cursor.expect("rbracket", "`]`");
        term = { kind: "TypeApp", callee: term, args, at: open.at };
      } else return term;
    }
  }

  private atom(): Term {
    const token = this.cursor.peek();
    const at = this.cursor.here;

    if (token?.kind === "identifier") {
      this.cursor.advance();
      return {
        kind: "Var",
        name: { text: token.text, at: token.at },
        at: token.at,
      };
    }
    if (token?.kind === "lparen") {
      this.cursor.advance();
      const inner = this.exp(EXPR);
      this.cursor.expect("rparen", "`)`");
      return inner;
    }
    if (token?.kind === "lbrace") {
      // Braces hold a block, so unlike parentheses they admit `let`.
      this.cursor.advance();
      const inner = this.cursor.block(true, () => this.exp(BLOCK));
      this.cursor.expect("rbrace", "`}`");
      return inner ?? { kind: "BadTerm", at };
    }

    this.cursor.report("an expression");
    return { kind: "BadTerm", at };
  }

  type(): TypeNode {
    const at = this.cursor.here;

    if (this.cursor.at("lbracket")) {
      const tyParams = this.typeBinders();
      const params = this.paramTypes();
      this.cursor.expect("arrow", "`->`, since a quantifier needs a function");
      return { kind: "FunType", tyParams, params, result: this.type(), at };
    }

    if (this.cursor.at("lparen")) {
      const params = this.paramTypes();
      if (this.cursor.accept("arrow") !== undefined) {
        return {
          kind: "FunType",
          tyParams: [],
          params,
          result: this.type(),
          at,
        };
      }
      // Not an arrow, so it was a parenthesised type -- and only one fits.
      const only = params[0];
      if (params.length === 1 && only !== undefined) return only;
      this.cursor.report("`->`, since a list of types is not a type");
      return { kind: "BadType", at };
    }

    const atom = this.atomType();
    if (this.cursor.accept("arrow") === undefined) return atom;
    return {
      kind: "FunType",
      tyParams: [],
      params: [atom],
      result: this.type(),
      at,
    };
  }

  private atomType(): TypeNode {
    const at = this.cursor.here;
    if (this.cursor.accept("unknown") !== undefined) {
      return { kind: "UnknownType", at };
    }
    if (this.cursor.accept("never") !== undefined) {
      return { kind: "NeverType", at };
    }

    const name = this.name("a type");
    if (name === undefined) return { kind: "BadType", at };

    const args: TypeNode[] = [];
    if (this.cursor.accept("lbracket") !== undefined) {
      do args.push(this.type()); while (
        this.cursor.accept("comma") !== undefined
      );
      this.cursor.expect("rbracket", "`]`");
    }
    return { kind: "NameType", name, args, at };
  }

  private paramTypes(): TypeNode[] {
    const params: TypeNode[] = [];
    if (this.cursor.expect("lparen", "`(`, a parameter list") === undefined) {
      return params;
    }
    if (!this.cursor.at("rparen")) {
      do params.push(this.type()); while (
        this.cursor.accept("comma") !== undefined
      );
    }
    this.cursor.expect("rparen", "`)`");
    return params;
  }

  /** `[A, B <: C]`. Bounds are parallel: a bound may not name its own group. */
  private typeBinders(): TypeBinder[] {
    const binders: TypeBinder[] = [];
    if (this.cursor.accept("lbracket") === undefined) return binders;
    if (!this.cursor.at("rbracket")) {
      do {
        const name = this.name("a type parameter");
        if (name === undefined) break;
        const bound = this.cursor.accept("subtype") === undefined
          ? undefined
          : this.type();
        binders.push(
          bound === undefined
            ? { name, at: name.at }
            : { name, bound, at: name.at },
        );
      } while (this.cursor.accept("comma") !== undefined);
    }
    this.cursor.expect("rbracket", "`]`");
    return binders;
  }

  private name(what: string): Name | undefined {
    const token = this.cursor.expect("identifier", what);
    return token === undefined ? undefined : { text: token.text, at: token.at };
  }
}

function wildcard(at: Position): Name {
  return { text: "_", at };
}
