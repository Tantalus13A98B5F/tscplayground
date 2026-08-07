/**
 * Recursive descent over the token array, layout already resolved.
 *
 * A block is `{ ... }` and an item ends at `;`, whether the author wrote those
 * or indented instead -- `layout` ran first. Nothing here reads a column, and
 * both halves of a block are tokens rather than one token and one rule.
 *
 * `parseProgram` is the entry point that matters. The top level is a flat *item*
 * loop -- declaration, binding, or the final expression -- whose bindings fold
 * into a `Let` chain at the end, so declarations never nest, never need lifting,
 * and `exp` has no `datatype` case at all.
 *
 * Errors are fatal to the construct being read: a rule reports and throws, and
 * only a run of items catches -- the item loop and the arm list, each resuming
 * at its next separator. Three things follow. No rule returns half a node; the
 * tree holds no recovery nodes; and a parse that reported anything yields no
 * tree at all, recovery being there to find the *other* errors rather than to
 * hand work downstream. Every loop consumes a token or breaks, so a malformed
 * file cannot spin.
 */

import {
  failed,
  hasErrors,
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
import { Cursor, rethrowUnexpected } from "./cursor.ts";

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
  return run(tokens, (parser) => parser.program());
}

/** Parse a single expression. For tests and the playground, not the pipeline. */
export function parseTerm(tokens: readonly Token[]): Result<TermNode> {
  return run(tokens, (parser) => parser.exp(BLOCK));
}

export function parseType(tokens: readonly Token[]): Result<TypeNode> {
  return run(tokens, (parser) => parser.type());
}

/**
 * Parse, or hand back the diagnostics alone.
 *
 * A dropped construct often leaves no node to stand in for it -- a block with
 * no result is not a term -- so any error withholds the value, rather than a
 * promise only some failures could keep. Warnings do not, being about what
 * parses.
 */
function run<T>(
  tokens: readonly Token[],
  parse: (parser: Parser) => T,
): Result<T> {
  const parser = new Parser(tokens);
  const { diagnostics } = parser.cursor;
  try {
    const value = parse(parser);
    return hasErrors(diagnostics)
      ? failed(diagnostics)
      : produced(value, diagnostics);
  } catch (failure) {
    rethrowUnexpected(failure);
    return failed(diagnostics);
  }
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
   * A block's contents: items separated by `;`, folded into a `Let` chain.
   *
   * A `let` names its result and anything else sequences under `_`, so the two
   * are one form with one separator rule -- stated once here, rather than per
   * item kind, where the top level and a nested body had drifted apart.
   *
   * Only an expression may end a block, and what follows settles which one: the
   * last expression read is buffered, and whatever outlives the loop is the
   * result. A `let` cannot end one, binding nothing if nothing follows it.
   *
   * `decls` is where declarations go, and having nowhere to put one is what
   * makes them top-level -- the invariant and the condition are one thing.
   *
   * One of the two places a failure is caught: an item is the unit recovery
   * works in, so a bad one costs itself and no more.
   */
  private stmts(decls?: TypeDecl[]): TermNode {
    const top = decls !== undefined;
    const rest = top ? "the rest of the program" : "the body";
    const binds: LetItem[] = [];
    /**
     * The last expression read, held back rather than bound: the block's result
     * if nothing follows it, a `_` binding as soon as something does. Buffering
     * lets the loop stay ignorant of which item is last.
     */
    let last: LetItem | undefined;
    /** Whether an item was dropped, so a missing result is already explained. */
    let dropped = false;

    while (this.moreItems()) {
      if (last !== undefined) {
        binds.push(last);
        last = undefined;
      }

      const mark = this.cursor.mark();
      try {
        if (top && this.cursor.at("datatype")) {
          decls.push(this.datatypeDecl());
        } else if (top && this.cursor.at("typedef")) {
          decls.push(this.aliasDecl());
        } else if (this.cursor.at("let")) {
          binds.push(this.letBinding());
        } else {
          const at = this.cursor.here;
          last = { name: wildcard(at), bound: this.exp(EXPR), at };
        }
        this.expectSeparator(rest);
      } catch (failure) {
        rethrowUnexpected(failure);
        dropped = true;
        this.cursor.skipToItem();
        this.cursor.accept("semi");
      }

      if (this.cursor.mark() === mark) this.cursor.advance(); // ensure progress
    }

    // An unset buffer is exactly the missing-result case -- unless an item was
    // dropped, the result being possibly what it took.
    const body = last?.bound ??
      (dropped ? this.cursor.abandon() : this.cursor.fail(
        `an expression to be ${top ? "the program's" : "the block's"} result`,
      ));

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
   * Whether an item can begin here. A closer ends the run, belonging to the
   * bracket around this block rather than to any item of it.
   */
  private moreItems(): boolean {
    const token = this.cursor.peek();
    return token.kind !== "eof" && !isCloser(token.kind);
  }

  /**
   * Step over the separator between two items. Nothing else marks where an
   * expression begins, so its absence is worth reporting -- unless the block
   * ends here, which is how the final expression gets to have none.
   */
  private expectSeparator(rest: string): void {
    if (this.cursor.accept("semi") !== undefined) return;
    if (!this.moreItems()) return;
    this.cursor.fail(`\`;\` or a new line, then ${rest}`);
  }

  /** `datatype Pair[A, B] where` then its constructor arms. */
  private datatypeDecl(): DatatypeDecl {
    const keyword = this.cursor.peek(); // the `datatype` the item loop saw
    this.cursor.advance();
    const name = this.ident("a type name");

    const typeParams = this.plainTypeParams();
    // A pure delimiter: nothing but constructors may follow it, which is what
    // lets layout open their block wherever it sits.
    this.cursor.expect("where", "`where`, then the constructors");
    const ctors = this.arms("constructor", () => this.ctorDecl());
    return { kind: "DatatypeDecl", name, typeParams, ctors, at: keyword.at };
  }

  /** `typedef Endo[A] = (A) -> A`. Transparent, so it has no constructors. */
  private aliasDecl(): AliasDecl {
    const keyword = this.cursor.peek(); // the `typedef` the item loop saw
    this.cursor.advance();
    const name = this.ident("a type name");
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
    do params.push(this.ident("a type parameter")); while (
      this.cursor.accept("comma") !== undefined
    );
    this.cursor.expect("rbracket", "`]`");
    return params;
  }

  private ctorDecl(): CtorDecl {
    const bar = this.cursor.peek(); // the `|` the arm loop saw
    this.cursor.advance();
    const name = this.ident("a constructor name");

    const params: CtorParam[] = [];
    if (this.cursor.accept("lparen") !== undefined) {
      if (!this.cursor.at("rparen")) {
        do params.push(this.ctorParam()); while (
          this.cursor.accept("comma") !== undefined
        );
      }
      this.cursor.expect("rparen", "`)`");
    }
    return { name, params, at: bar.at };
  }

  private ctorParam(): CtorParam {
    const name = this.ident("a parameter name");
    // Required: a field has nothing to infer an annotation from.
    this.cursor.expect(
      "colon",
      "`:`, since every constructor parameter is annotated",
    );
    return { name, annotation: this.type(), at: name.at };
  }

  /**
   * A run of `|` arms, after `with` or `where` -- and the other place a failure
   * is caught, `|` delimiting items much as `;` does.
   *
   * The block is required, and only here is its absence reported: layout opens
   * one wherever the arms clear the column their keyword set, and says nothing
   * when they do not. Arms without one bind innermost with no way to spell the
   * other reading, so reading them would be guessing which construct they belong
   * to. Placement past that column is free -- tidying ragged arms is a
   * formatter's job.
   *
   * Having consumed no `{`, consume no `}`: it belongs to whatever encloses
   * this, and taking it would end *that* here, one misindented arm list costing
   * the construct it sits in. The whole item goes instead, the item loop
   * skipping past these arms on its way to the next `;`.
   */
  private arms<T>(what: string, parse: () => T): T[] {
    const results: T[] = [];
    const braced = this.cursor.accept("lbrace") !== undefined;

    if (!braced && this.cursor.at("bar")) {
      this.cursor.fail(`the ${what}s, indented past the start of this item`);
    }

    let dropped = false;
    while (this.cursor.at("bar")) {
      const mark = this.cursor.mark();
      try {
        results.push(parse());
      } catch (failure) {
        rethrowUnexpected(failure);
        dropped = true;
        this.cursor.skipToArm();
      }
      if (this.cursor.mark() === mark) break;
    }

    // Before the `}`, so the caret lands where an arm was wanted rather than
    // past the run holding none -- and silently if every arm was dropped, the
    // emptiness being those failures' doing.
    if (results.length === 0) {
      if (dropped) this.cursor.abandon();
      this.cursor.fail(`at least one ${what}`);
    }
    if (braced) this.cursor.expect("rbrace", `\`}\`, or another ${what}`);
    return results;
  }

  /** `let x = e`, without the separator or the body that follows it. */
  private letBinding(): LetItem {
    const at = this.cursor.here; // the `let` the item loop saw
    this.cursor.advance();
    const name = this.ident("a name to bind");
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
   * body makes, a line-ending opener being what turns one into the other.
   *
   * A body short of the column its opener set is neither, layout having ended
   * the item before it. Saying what was wanted names the fix, where `an
   * expression` would land on the line the author wrote as the body and deny it
   * was one.
   */
  private blockOrExp(what: string): TermNode {
    if (this.cursor.at("lbrace")) return this.block();
    if (this.cursor.at("semi") || !this.moreItems()) this.cursor.fail(what);
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
    this.cursor.expect("lparen", "`(`, a parameter list");
    if (!this.cursor.at("rparen")) {
      do {
        const name = this.ident("a parameter name");
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

  private matchArm(): MatchArm {
    const bar = this.cursor.peek(); // the `|` the arm loop saw
    this.cursor.advance();
    const pattern = this.matchPat();
    this.cursor.expect("arrow", "`->`");
    // Past its `|`, not level with it: the arm list's items begin one column
    // right of the bar, so a body there is the next item rather than this one's.
    const body = this.blockOrExp("the arm's body, indented past its `|`");
    return { pattern, body, at: bar.at };
  }

  /**
   * `_`, `C`, or `C(x, y)`. A name here is always a constructor and one inside
   * the parentheses always a binder, so a misspelt constructor cannot quietly
   * become a catch-all -- nor can one that fails to parse, the arm it heads
   * being dropped whole rather than left covering anything.
   */
  private matchPat(): MatchPat {
    const name = this.ident("a constructor name or `_`");
    if (name.text === WILDCARD) return { kind: "PWild", at: name.at };

    const args: Ident[] = [];
    if (this.cursor.accept("lparen") !== undefined) {
      if (!this.cursor.at("rparen")) {
        do args.push(this.ident("a name to bind")); while (
          this.cursor.accept("comma") !== undefined
        );
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

    this.cursor.fail("an expression");
  }

  /**
   * A type, possibly wrapped in the block a line-ending `=` or `->` opened
   * around it. Layout does not know a type from a term, and needs not: a block
   * holding one type is just that type.
   */
  type(): TypeNode {
    if (this.cursor.at("lbrace")) {
      this.cursor.advance();
      const inner = this.type();
      this.cursor.expect(
        "rbrace",
        "`}`, since a block in a type holds one type",
      );
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
      this.cursor.fail("`->`, since a list of types is not a type");
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
    this.cursor.expect("lparen", "`(`, a parameter list");
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

  private ident(what: string): Ident {
    const token = this.cursor.expect("identifier", what);
    return { text: token.text, at: token.at };
  }
}

/**
 * An ordinary identifier, not a token kind of its own. So everything that walks
 * binders -- the duplicate check, the shadowing warning, the context -- must
 * exempt it by name.
 */
export const WILDCARD = "_";

function wildcard(at: Position): Ident {
  return { text: WILDCARD, at };
}
