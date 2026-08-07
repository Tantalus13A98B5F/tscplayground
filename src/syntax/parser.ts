/**
 * Recursive descent over the token array, with layout already resolved.
 *
 * `prescan` runs first, so a block is `{ ... }` and an item ends at `;`
 * whether the author wrote those or indented instead. Nothing here reads a
 * column, and the two halves of block structure -- where one opens and where it
 * ends -- are both tokens rather than one token and one arithmetic rule.
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
import { isCloser, type Token } from "./lexer.ts";
import { Cursor } from "./cursor.ts";

/** `let` and sequencing: the forms that run to the end of their block. */
const BLOCK = 0;
/** An expression that stops before a `;` or the end of its block. */
const EXPR = 1;
/**
 * `fn` and `match`: greedy to the right, but nestable inside an argument. Infix
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
    return { decls, term: this.stmts(decls), at };
  }

  /**
   * A block's contents: items separated by `;`, folded into a `Let` chain. A
   * `let` names its result and anything else sequences under `_`, so the two
   * are one form with one separator rule -- stated here rather than once per
   * item kind, where the top level and a nested body had drifted apart on both
   * the message and the recovery.
   *
   * Only an expression may end a block, and which one does is settled by what
   * follows rather than by the loop: the last expression read is buffered, and
   * whatever outlives the loop is the result. A `let` cannot end one, since a
   * binding with nothing following it binds nothing.
   *
   * `decls` is where declarations go. Without a sink there is nowhere to put
   * one, which is exactly what makes them top-level -- the invariant and the
   * condition are the same thing rather than two that must agree.
   */
  private stmts(decls?: TypeDecl[]): TermNode {
    const top = decls !== undefined;
    const rest = top ? "the rest of the program" : "the body";
    const binds: LetItem[] = [];
    /**
     * The last expression read, held back rather than bound: it is the block's
     * result if nothing follows it, and a `_` binding as soon as something
     * does. Buffering is what lets the loop stay ignorant of which item is last.
     */
    let last: LetItem | undefined;

    while (this.moreItems()) {
      if (last !== undefined) {
        binds.push(last);
        last = undefined;
      }

      const mark = this.cursor.mark();
      if (top && this.cursor.at("datatype")) {
        const decl = this.datatypeDecl();
        if (decl !== undefined) decls.push(decl);
      } else if (top && this.cursor.at("typedef")) {
        const alias = this.aliasDecl();
        if (alias !== undefined) decls.push(alias);
      } else if (this.cursor.at("let")) {
        binds.push(this.letBinding());
      } else {
        const at = this.cursor.here;
        const term = this.exp(EXPR);
        // Having consumed nothing it is no result but a token nothing can use,
        // which the progress guard below has to step over.
        if (this.cursor.mark() !== mark) {
          last = { name: wildcard(at), bound: term, at };
        }
      }

      if (this.cursor.mark() === mark) this.cursor.advance(); // ensure progress
      this.skipSeparator(rest);
    }

    // A `let` cannot end a block -- a binding with nothing following it binds
    // nothing -- so an unset buffer is exactly the missing-result case.
    let body = last?.bound;
    if (body === undefined) {
      this.cursor.report(
        `an expression to be ${top ? "the program's" : "the block's"} result`,
      );
      body = { kind: "BadTerm", at: this.cursor.here };
    }

    return binds.reduceRight<TermNode>(
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
  }

  /**
   * Whether an item can begin here. A closer ends the run: it belongs to the
   * bracket that opened this block, which no item of it may consume.
   */
  private moreItems(): boolean {
    const token = this.cursor.peek();
    return token.kind !== "eof" && !isCloser(token.kind);
  }

  /**
   * Step over the separator between two items. Nothing marks where an
   * expression begins, so its absence is worth reporting -- unless the block
   * ends here, which is how its final expression gets to have none.
   */
  private skipSeparator(rest: string): void {
    if (this.cursor.accept("semi") !== undefined) return;
    if (!this.moreItems()) return;
    this.cursor.report(`\`;\` or a new line, then ${rest}`);
    this.cursor.skipStray();
    this.cursor.accept("semi");
  }

  /** `datatype Pair[A, B] where` then its constructor arms. */
  private datatypeDecl(): DatatypeDecl | undefined {
    const keyword = this.cursor.accept("datatype");
    if (keyword === undefined) return undefined;
    const name = this.ident("a type name");
    if (name === undefined) return undefined;

    const typeParams = this.plainTypeParams();
    // A pure delimiter: nothing but constructors may follow it, which is what
    // lets the prescan open their block wherever it sits.
    this.cursor.expect("where", "`where`, then the constructors");
    const ctors = this.arms("constructor", () => this.ctorDecl());
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
   * A run of `|` arms, after `with` or `where`.
   *
   * The block is required, and this is the only place its absence is reported:
   * the prescan opens one wherever the arms clear the column their keyword set
   * and says nothing when they do not. Arms without one bind innermost with no
   * way to spell the other reading, so reading them would be guessing at which
   * construct they belong to; they are dropped whole instead. Placement past
   * that column is free, and tidying ragged arms is a formatter's job.
   *
   * Having consumed no `{`, consume no `}` -- which is why the wreckage goes to
   * `skipStray` and not to `closeBrace`. Without a block of its own the next `}`
   * belongs to whatever encloses this, and taking it would end *that* here: one
   * misindented arm list would cost the construct it sits in.
   */
  private arms<T>(what: string, parse: () => T | undefined): T[] {
    const results: T[] = [];
    const braced = this.cursor.accept("lbrace") !== undefined;

    if (!braced && this.cursor.at("bar")) {
      this.cursor.report(`the ${what}s, indented past the start of this item`);
      this.cursor.skipStray();
      return results;
    }

    while (this.cursor.at("bar")) {
      const mark = this.cursor.mark();
      const parsed = parse();
      if (parsed !== undefined) results.push(parsed);
      if (this.cursor.mark() === mark) break;
    }

    if (braced) this.closeBrace(`\`}\`, or another ${what}`);
    if (results.length === 0) this.cursor.report(`at least one ${what}`);
    return results;
  }

  /**
   * The `}` ending a brace run that holds no items -- an arm list, a type. A
   * `;` inside one is wreckage rather than a place to resume, so recovery
   * skips past it; `stmts` needs none of this, a `;` there being its business.
   */
  private closeBrace(expected: string): void {
    if (!this.cursor.at("rbrace")) {
      this.cursor.report(expected);
      this.cursor.skipStray(true);
    }
    this.cursor.accept("rbrace");
  }

  /** `let x = e`, without the separator or the body that follows it. */
  private letBinding(): LetItem {
    const at = this.cursor.here; // the `let` the item loop saw
    this.cursor.advance();
    const name = this.ident("a name to bind") ?? wildcard(at);
    const annotation = this.cursor.accept("colon") === undefined
      ? undefined
      : this.type();
    this.cursor.expect("equals", "`=`");
    const bound = this.blockOrExp("the bound value, indented past the `let`");
    return annotation === undefined
      ? { name, bound, at }
      : { name, annotation, bound, at };
  }

  /**
   * A block here, or the expression continuing where it is -- the choice every
   * body makes, a line-ending opener being what turned the one into the other.
   *
   * A body short of the column its opener set is neither: layout ended the item
   * before it, so it is gone by the time we look. Saying what was wanted names
   * the fix, where `an expression` would land on the line the author wrote as
   * the body and deny it was one.
   */
  private blockOrExp(what: string): TermNode {
    if (this.cursor.at("lbrace")) return this.block();
    if (this.cursor.at("semi") || !this.moreItems()) this.cursor.report(what);
    return this.exp(EXPR);
  }

  /** `{ ... }`, the only place a term block is entered. Callers see the `{`. */
  private block(): TermNode {
    this.cursor.advance();
    const inner = this.stmts();
    this.cursor.expect("rbrace", "`}`");
    return inner;
  }

  exp(prec: number): TermNode {
    // A block is a run of items, `let` and sequencing alike; `stmts` owns both.
    if (prec <= BLOCK) return this.stmts();

    if (prec <= PREFIX && this.cursor.at("fn")) return this.abs();
    if (prec <= PREFIX && this.cursor.at("match")) return this.match();

    return this.postfix();
  }

  /** `fn (x: A) -> e`, or `fn [T <: A](x: T) -> e` -- one binder, both worlds. */
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
    this.cursor.expect("arrow", "`->`, then the body");
    const body = this.blockOrExp("the function's body, indented past the `fn`");
    return { kind: "Abs", typeParams, params, body, at };
  }

  private match(): TermNode {
    const keyword = this.cursor.peek();
    this.cursor.advance();
    const scrutinee = this.exp(PREFIX + 1);
    this.cursor.expect("with", "`with`, then the arms");
    const arms = this.arms("arm", () => this.matchArm());
    return { kind: "Match", scrutinee, arms, at: keyword.at };
  }

  private matchArm(): MatchArm | undefined {
    const bar = this.cursor.accept("bar");
    if (bar === undefined) return undefined;
    const pattern = this.matchPat();
    this.cursor.expect("arrow", "`->`");
    // Past its `|`, not level with it: the arm list's items begin one column
    // right of the bar, so a body there is the next item rather than this one's.
    const body = this.blockOrExp("the arm's body, indented past its `|`");
    return { pattern, body, at: bar.at };
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
      if (open.kind === "lparen") {
        this.cursor.advance();
        const args: TermNode[] = [];
        if (!this.cursor.at("rparen")) {
          do args.push(this.exp(EXPR)); while (
            this.cursor.accept("comma") !== undefined
          );
        }
        this.cursor.expect("rparen", "`)`");
        term = { kind: "App", callee: term, args, at: open.at };
      } else if (open.kind === "lbracket") {
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
    const at = token.at;

    if (token.kind === "identifier") {
      this.cursor.advance();
      return {
        kind: "Var",
        name: { text: token.text, at: token.at },
        at: token.at,
      };
    }
    if (token.kind === "lparen") {
      this.cursor.advance();
      const inner = this.exp(EXPR);
      this.cursor.expect("rparen", "`)`");
      return inner;
    }
    // Braces hold a block, so unlike parentheses they admit `let`.
    if (token.kind === "lbrace") return this.block();

    this.cursor.report("an expression");
    return { kind: "BadTerm", at };
  }

  /**
   * A type, possibly wrapped in the block a line-ending `=` or `->` opened
   * around it. The prescan does not know a type from a term -- and needs not,
   * since a block holding one type is just that type.
   */
  type(): TypeNode {
    if (this.cursor.at("lbrace")) {
      this.cursor.advance();
      const inner = this.type();
      this.closeBrace("`}`, since a block in a type holds one type");
      return inner;
    }

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
