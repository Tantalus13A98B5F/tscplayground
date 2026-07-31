/**
 * Recursive descent over the token array, with layout resolved by `Cursor`.
 *
 * `parseProgram` is the only entry point that matters. The top level is a flat
 * *item* loop -- a declaration, a binding, or the final expression -- whose
 * bindings fold into a `Let` chain at the end, so declarations never nest and
 * never need lifting, and `exp` has no `datatype` case at all.
 *
 * Recovery returns `BadTerm`/`BadType` and carries on. Every loop either
 * consumes a token or breaks, so a malformed file cannot spin.
 */

import {
  type Position,
  produced,
  type Result,
} from "../diagnostics/diagnostic.ts";
import type {
  AliasDecl,
  CtorDecl,
  CtorParam,
  DatatypeDecl,
  Ident,
  LetItem,
  MatchArm,
  MatchPat,
  Param,
  Program,
  TermNode,
  TypeDecl,
  TypeNode,
  TypeParam,
} from "./ast.ts";
import type { Token } from "./lexer.ts";
import { Cursor } from "./layout.ts";

/** `let` and sequencing: the forms that run to the end of their block. */
const BLOCK = 0;
/** An expression that stops before a `;` or a new line. */
const EXPR = 1;
/**
 * `\` and `match`: greedy to the right, but nestable inside an argument. Infix
 * operators belong *above* this, so a lambda swallows `+ 1` but cannot be an
 * operand.
 */
const PREFIX = 20;

export function parseProgram(tokens: readonly Token[]): Result<Program> {
  const parser = new Parser(tokens);
  const program = parser.program();
  return produced(program, parser.cursor.diagnostics);
}

/** Parse a single expression. For tests and the playground, not the pipeline. */
export function parseTerm(tokens: readonly Token[]): Result<TermNode> {
  const parser = new Parser(tokens);
  const term = parser.exp(BLOCK);
  return produced(term, parser.cursor.diagnostics);
}

export function parseType(tokens: readonly Token[]): Result<TypeNode> {
  const parser = new Parser(tokens);
  const type = parser.type();
  return produced(type, parser.cursor.diagnostics);
}

class Parser {
  readonly cursor: Cursor;

  constructor(tokens: readonly Token[]) {
    this.cursor = new Cursor(tokens);
  }

  program(): Program {
    const at = this.cursor.here;
    const decls: TypeDecl[] = [];
    const binds: LetItem[] = [];
    let body: TermNode | undefined;

    while (!this.cursor.isEof) {
      const mark = this.cursor.mark();

      if (this.cursor.at("datatype")) {
        const decl = this.datatypeDecl();
        if (decl !== undefined) decls.push(decl);
      } else if (this.cursor.at("typedef")) {
        const alias = this.aliasDecl();
        if (alias !== undefined) decls.push(alias);
      } else if (this.cursor.at("let")) {
        binds.push(this.letBinding());
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
      if (!this.cursor.trySemiNewline()) {
        this.cursor.report("`;` or a new line, then the rest of the program");
        this.cursor.skipToBlockStart();
      }
      if (this.cursor.mark() === mark) this.cursor.advance(); // ensure progress
    }

    if (body === undefined) {
      this.cursor.report("an expression to be the program's result");
      body = { kind: "BadTerm", at: this.cursor.here };
    }

    const term = binds.reduceRight<TermNode>(
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

  /** `datatype Pair[A, B] =` then its constructor arms. */
  private datatypeDecl(): DatatypeDecl | undefined {
    const keyword = this.cursor.accept("datatype");
    if (keyword === undefined) return undefined;
    const name = this.ident("a type name");
    if (name === undefined) return undefined;

    const typeParams = this.plainTypeParams();

    // Purely for symmetry with `let`; the arm block opens at the first `|`
    // either way, on this line or the next.
    this.cursor.expect("equals", "`=`");
    const ctors = this.barBlock("constructor", keyword, () => this.ctorDecl());
    return { kind: "DatatypeDecl", name, typeParams, ctors, at: keyword.at };
  }

  /** `typedef Endo[A] = (A) -> A`. Transparent, so it has no constructors. */
  private aliasDecl(): AliasDecl | undefined {
    const keyword = this.cursor.accept("typedef");
    if (keyword === undefined) return undefined;
    const name = this.ident("a type name");
    if (name === undefined) return undefined;
    const typeParams = this.plainTypeParams();
    this.cursor.expect("equals", "`=`");
    return {
      kind: "AliasDecl",
      name,
      typeParams,
      body: this.type(),
      at: keyword.at,
    };
  }

  /** `[A, B]`, the unbounded binding position shared by both declarations. */
  private plainTypeParams(): Ident[] {
    const params: Ident[] = [];
    if (this.cursor.accept("lbracket") === undefined) return params;
    do {
      const param = this.ident("a type parameter");
      if (param === undefined) break;
      params.push(param);
    } while (this.cursor.accept("comma") !== undefined);
    this.cursor.expect("rbracket", "`]`");
    return params;
  }

  private ctorDecl(): CtorDecl | undefined {
    const bar = this.cursor.accept("bar");
    if (bar === undefined) return undefined;
    const name = this.ident("a constructor name");
    if (name === undefined) return undefined;

    const params: CtorParam[] = [];
    if (this.cursor.accept("lparen") !== undefined) {
      if (!this.cursor.at("rparen")) {
        do {
          const param = this.ctorParam();
          if (param === undefined) break;
          params.push(param);
        } while (this.cursor.accept("comma") !== undefined);
      }
      this.cursor.expect("rparen", "`)`");
    }
    return { name, params, at: bar.at };
  }

  private ctorParam(): CtorParam | undefined {
    const name = this.ident("a parameter name");
    if (name === undefined) return undefined;
    // Required: a field has nothing to infer an annotation from.
    this.cursor.expect(
      "colon",
      "`:`, since every constructor parameter is annotated",
    );
    return { name, annotation: this.type(), at: name.at };
  }

  /**
   * A run of `|` arms, forming a block at the first one's column.
   *
   * A keyword starting its own line owns that column, so its arms may sit there
   * too. One that does not must have its arms indented past the enclosing block,
   * since that column is already spoken for: in `| A -> match y`, arms at the
   * outer column would be ambiguous between the two matches. The indent is what
   * makes nesting explicit instead of a dangling-else convention.
   *
   * Placement past that is free -- an indented line is a continuation, and a
   * continuation carries an arm as the original line could. `|` is reserved and
   * no expression consumes it, so only one parse ever exists; tidying ragged
   * arms is a formatter's job.
   */
  private barBlock<T>(
    what: string,
    keyword: Token,
    parse: () => T | undefined,
  ): T[] {
    const results: T[] = [];
    this.cursor.block(!keyword.first, () => {
      while (this.cursor.tryBarNewline()) {
        const mark = this.cursor.mark();
        const parsed = parse();
        if (parsed !== undefined) results.push(parsed);
        if (this.cursor.mark() === mark) break;
      }
    });
    if (results.length === 0) this.cursor.report(`at least one ${what}`);
    // Banned rather than given a meaning: in `| A -> f(y); g(z)` the two
    // readings cannot be told apart, and both have another way to be said.
    if (this.cursor.raw.kind === "semi") {
      this.cursor.complain(
        "`;` cannot follow an arm: indent the arm's body to sequence within " +
          "it, or wrap the whole form in braces to sequence after it",
      );
    }
    return results;
  }

  /** Shared by the item loop and `exp`, which differ only in what follows. */
  private letBinding(): LetItem {
    const keyword = this.cursor.accept("let");
    const at = keyword?.at ?? this.cursor.here;
    const name = this.ident("a name to bind") ?? wildcard(at);
    const annotation = this.cursor.accept("colon") === undefined
      ? undefined
      : this.type();
    this.cursor.expect("equals", "`=`");
    const bound = this.blockOrExp(EXPR);
    return annotation === undefined
      ? { name, bound, at }
      : { name, annotation, bound, at };
  }

  /**
   * A newline here opens an indented block; otherwise the expression continues
   * on this line. One function, and the only place blocks are introduced.
   */
  private blockOrExp(prec: number): TermNode {
    if (!this.cursor.raw.first) return this.exp(prec);
    const at = this.cursor.here;
    return this.cursor.block(true, () => this.exp(BLOCK)) ??
      { kind: "BadTerm", at };
  }

  exp(prec: number): TermNode {
    if (prec <= BLOCK && this.cursor.at("let")) {
      const head = this.letBinding();
      if (!this.cursor.trySemiNewline()) {
        this.cursor.report("`;` or a new line, then the body");
      }
      return { kind: "Let", ...head, body: this.exp(BLOCK) };
    }

    if (prec <= BLOCK) {
      // `e1; e2` binds nothing, but keeps its place once effects exist. Prefix
      // forms reach this too, so they can head a sequence rather than strand
      // what follows; `let` is above only because it takes the rest as its body.
      const at = this.cursor.here;
      const first = this.exp(EXPR);
      if (!this.cursor.trySemiNewline()) return first;
      return {
        kind: "Let",
        name: wildcard(at),
        bound: first,
        body: this.exp(BLOCK),
        at,
      };
    }

    if (prec <= PREFIX && this.cursor.at("lambda")) return this.abs();
    if (prec <= PREFIX && this.cursor.at("match")) return this.match();

    return this.postfix();
  }

  /** `\(x: A) e`, or `\[T <: A](x: T) e` -- one binder, both worlds. */
  private abs(): TermNode {
    const at = this.cursor.here;
    this.cursor.advance();
    const typeParams = this.cursor.at("lbracket")
      ? this.boundedTypeParams()
      : [];
    const params: Param[] = [];
    if (this.cursor.expect("lparen", "`(`, a parameter list") !== undefined) {
      if (!this.cursor.at("rparen")) {
        do {
          const name = this.ident("a parameter name");
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
    return { kind: "Abs", typeParams, params, body: this.blockOrExp(EXPR), at };
  }

  private match(): TermNode {
    const keyword = this.cursor.raw;
    this.cursor.advance();
    const scrutinee = this.exp(PREFIX + 1);
    const arms = this.barBlock("arm", keyword, () => this.matchArm());
    return { kind: "Match", scrutinee, arms, at: keyword.at };
  }

  private matchArm(): MatchArm | undefined {
    const bar = this.cursor.accept("bar");
    if (bar === undefined) return undefined;
    const pattern = this.matchPat();
    this.cursor.expect("arrow", "`->`");
    return { pattern, body: this.blockOrExp(EXPR), at: bar.at };
  }

  /**
   * `_`, `C`, or `C(x, y)`. A name in this position is always a constructor and
   * a name inside the parentheses is always a binder, so a misspelt constructor
   * cannot quietly become a catch-all -- nor can one that fails to parse, which
   * recovers as `PBad` rather than as the wildcard it resembles.
   */
  private matchPat(): MatchPat {
    const name = this.ident("a constructor name or `_`");
    if (name === undefined) return { kind: "PBad", at: this.cursor.here };
    if (name.text === WILDCARD) return { kind: "PWild", at: name.at };

    const args: Ident[] = [];
    if (this.cursor.accept("lparen") !== undefined) {
      if (!this.cursor.at("rparen")) {
        do {
          const bound = this.ident("a name to bind");
          if (bound === undefined) break;
          args.push(bound);
        } while (this.cursor.accept("comma") !== undefined);
      }
      this.cursor.expect("rparen", "`)`");
    }
    return { kind: "PCtor", name, args, at: name.at };
  }

  /** The postfix tier: application and instantiation, both left-associative. */
  private postfix(): TermNode {
    let term = this.atom();
    for (;;) {
      const open = this.cursor.peek();
      if (open?.kind === "lparen") {
        this.cursor.advance();
        const args: TermNode[] = [];
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

  private atom(): TermNode {
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
      const typeParams = this.boundedTypeParams();
      const params = this.parenTypes();
      this.cursor.expect("arrow", "`->`, since a quantifier needs a function");
      return { kind: "FunType", typeParams, params, result: this.type(), at };
    }

    if (this.cursor.at("lparen")) {
      const params = this.parenTypes();
      if (this.cursor.accept("arrow") !== undefined) {
        return {
          kind: "FunType",
          typeParams: [],
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
      typeParams: [],
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

    const name = this.ident("a type");
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

  private parenTypes(): TypeNode[] {
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
  private boundedTypeParams(): TypeParam[] {
    const binders: TypeParam[] = [];
    if (this.cursor.accept("lbracket") === undefined) return binders;
    if (!this.cursor.at("rbracket")) {
      do {
        const name = this.ident("a type parameter");
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

  private ident(what: string): Ident | undefined {
    const token = this.cursor.expect("identifier", what);
    return token === undefined ? undefined : { text: token.text, at: token.at };
  }
}

/**
 * An ordinary identifier, not a token kind of its own, so everything that walks
 * binders -- the duplicate check, the shadowing warning, the context -- must
 * exempt it by name.
 */
export const WILDCARD = "_";

function wildcard(at: Position): Ident {
  return { text: WILDCARD, at };
}
