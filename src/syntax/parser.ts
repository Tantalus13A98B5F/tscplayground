/**
 * Recursive descent over the token array, layout already resolved.
 *
 * A block is `{ ... }` and its parts end at `;`, whether the author wrote those
 * or indented instead -- `layout` ran first. Nothing here reads a column, and
 * both halves of a block are tokens rather than one token and one rule.
 *
 * `parseProgram` is the entry point that matters. The top level is one flat
 * loop over a block's parts -- declaration, binding, or the final expression --
 * whose bindings fold into a `Let` chain at the end, so declarations never nest,
 * never need lifting, and `exp` has no `datatype` case at all.
 *
 * Errors are fatal to the construct being read: a rule reports and throws, and
 * only the two loops over a `;`- or `|`-separated run catch -- `blockBody` and
 * `arms` -- each resuming at its next separator. Three things follow. No rule
 * returns half a node; the tree holds no recovery nodes; and a parse that
 * reported anything yields no tree at all, recovery being there to find the
 * *other* errors rather than to hand work downstream. Every loop consumes a
 * token or breaks, so a malformed file cannot spin.
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
  BindingIdent,
  CtorDecl,
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
import { isCloser, type Token, type TokenKind } from "./lexer.ts";
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
 * promise only some failures could keep.
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
    return { decls, term: this.blockBody(decls), at };
  }

  /**
   * A block's contents, folded into a `Let` chain: a declaration, a binding, or
   * the result, each ended by `;` and the last by the `}` or eof instead.
   *
   * A `let` names its result and anything else sequences under `_`, so the two
   * are one form under one separator rule, stated once.
   *
   * Only an expression may end a block, and what follows settles which one: the
   * last expression read is buffered, and whatever outlives the loop is the
   * result. A `let` cannot end one, binding nothing if nothing follows it.
   *
   * `decls` is where declarations go, and having nowhere to put one is what
   * makes them top-level -- the invariant and the condition are one thing.
   *
   * One of the two places a failure is caught: everything between two `;` is
   * what recovery drops, so a bad one costs itself and no more.
   */
  private blockBody(decls?: TypeDecl[]): TermNode {
    const top = decls !== undefined;
    const what = top ? "program" : "block";
    const binds: LetItem[] = [];
    /**
     * The last expression read, held back rather than bound: the block's result
     * if nothing follows it, a `_` binding as soon as something does. Buffering
     * lets the loop stay ignorant of which read is the last one.
     */
    let last: TermNode | undefined;
    /** Whether one was dropped, so a missing result is already explained. */
    let dropped = false;

    while (!this.atBlockEnd()) {
      if (last !== undefined) {
        binds.push({ name: wildcard(last.at), bound: last, at: last.at });
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
          last = this.exp(EXPR);
        }
        this.expectSemi(what);
      } catch (failure) {
        rethrowUnexpected(failure);
        dropped = true;
        this.cursor.skipToSemi();
        this.cursor.accept("semi");
      }

      // The one loop whose progress is not structural: every branch above ends
      // in a rule that consumes or throws, but that is a claim about the whole
      // expression grammar, and the cost of its being wrong once is a hang.
      if (this.cursor.mark() === mark) this.cursor.advance();
    }

    // An unset buffer is exactly the missing-result case -- unless something
    // was dropped, the result being possibly what it took.
    const result = last ??
      (dropped
        ? this.cursor.abandon()
        : this.cursor.fail(`an expression to be the ${what}'s result`));

    // A `LetItem` is a `Let` short of its body, so each fold supplies one.
    return binds.reduceRight<TermNode>(
      (body, bind) => ({ kind: "Let", ...bind, body }),
      result,
    );
  }

  /**
   * Whether the block is over. A closer ends it, belonging to the bracket
   * around the block rather than to anything inside it.
   */
  private atBlockEnd(): boolean {
    const token = this.cursor.peek();
    return token.kind === "eof" || isCloser(token.kind);
  }

  /**
   * Step over the `;` between two of a block's parts. Nothing else marks where
   * the next expression begins, so its absence is worth reporting -- unless the
   * block ends here, which is how the final expression gets to have none.
   */
  private expectSemi(what: string): void {
    if (this.cursor.accept("semi") !== undefined) return;
    if (this.atBlockEnd()) return;
    this.cursor.fail(`\`;\` or a new line, then the rest of the ${what}`);
  }

  /** `datatype Pair[A, B] where` then its constructor arms. */
  private datatypeDecl(): DatatypeDecl {
    const keyword = this.cursor.peek(); // the `datatype` the block loop saw
    this.cursor.advance();
    const name = this.declName("a type name");

    const typeParams = this.cursor.at("lbracket")
      ? this.plainTypeBinders()
      : [];
    // A pure delimiter: nothing but constructors may follow it, which is what
    // lets layout open their block wherever it sits.
    this.cursor.expect("where", "`where`, then the constructors");
    const ctors = this.arms("constructor", (at) => this.ctorDecl(at));
    return { kind: "DatatypeDecl", name, typeParams, ctors, at: keyword.at };
  }

  /** `typedef Endo[A] = (A) -> A`. Transparent, so it has no constructors. */
  private aliasDecl(): AliasDecl {
    const keyword = this.cursor.peek(); // the `typedef` the block loop saw
    this.cursor.advance();
    const name = this.declName("a type name");
    const typeParams = this.cursor.at("lbracket")
      ? this.plainTypeBinders()
      : [];
    this.cursor.expect("equals", "`=`");
    return {
      kind: "AliasDecl",
      name,
      typeParams,
      body: this.type(),
      at: keyword.at,
    };
  }

  private ctorDecl(at: Position): CtorDecl {
    const name = this.declName("a constructor name");
    // A constructor is an ordinary function, so its fields are a domain -- and
    // absent entirely for a nullary one, which takes no `()` at all.
    const params = this.cursor.at("lparen") ? this.domainTypes() : [];
    return { name, params, at };
  }

  /**
   * A run of `|` arms, after `with` or `where` -- and the other place a failure
   * is caught, `|` delimiting items much as `;` does. The `|` is read here, so
   * each arm rule is handed the position of its own and the loop is sure to
   * advance whatever that rule does.
   *
   * The block is required, and only here is its absence reported: layout opens
   * one wherever the arms clear the column their keyword set, and says nothing
   * when they do not. Arms short of it bind innermost with no way to spell the
   * other reading, so reading them would be guessing which construct they belong
   * to. Placement past that column is free -- tidying ragged arms is a
   * formatter's job.
   *
   * So there is no unbraced run to read: a `}` here always closes a `{` this
   * consumed, never one belonging to whatever encloses it.
   */
  private arms<T>(what: string, parseArm: (at: Position) => T): T[] {
    const missing = `at least one ${what}`;
    if (this.cursor.accept("lbrace") === undefined) {
      this.cursor.fail(
        this.cursor.at("bar")
          ? `the ${what}s, indented past the start of this item`
          : missing,
      );
    }

    const results: T[] = [];
    let dropped = false;
    while (this.cursor.at("bar")) {
      const bar = this.cursor.peek();
      this.cursor.advance();
      try {
        results.push(parseArm(bar.at));
      } catch (failure) {
        rethrowUnexpected(failure);
        dropped = true;
        this.cursor.skipToBar();
      }
    }

    // Before the `}`, so the caret lands where an arm was wanted rather than
    // past the run holding none -- and silently if every arm was dropped, the
    // emptiness being those failures' doing.
    if (results.length === 0) {
      if (dropped) this.cursor.abandon();
      this.cursor.fail(missing);
    }
    this.cursor.expect("rbrace", `\`}\`, or another ${what}`);
    return results;
  }

  /** `let x = e`, without the separator or the body that follows it. */
  private letBinding(): LetItem {
    const at = this.cursor.here; // the `let` the block loop saw
    this.cursor.advance();
    const name = this.binderName("a name to bind");
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
   * A body short of the column its opener set is neither, layout having closed
   * the construct before it. Saying what was wanted names the fix, where `an
   * expression` would land on the line the author wrote as the body and deny it
   * was one.
   */
  private blockOrExp(what: string): TermNode {
    if (this.cursor.at("lbrace")) return this.block();
    if (this.cursor.at("semi") || this.atBlockEnd()) this.cursor.fail(what);
    return this.exp(EXPR);
  }

  /** `{ ... }`, the only place a term block is entered. Callers see the `{`. */
  private block(): TermNode {
    this.cursor.advance();
    const inner = this.blockBody();
    this.cursor.expect("rbrace", "`}`");
    return inner;
  }

  exp(prec: number): TermNode {
    // `let` and sequencing both run to the end of the block; `blockBody` owns
    // the pair, so neither has a case here.
    if (prec <= BLOCK) return this.blockBody();

    if (prec <= PREFIX) {
      if (this.cursor.at("fn")) return this.abs();
      if (this.cursor.at("match")) return this.match();
    }

    return this.postfix();
  }

  /** `fn (x: A) -> e`, or `fn [T <: A](x: T) -> e` -- one binder, both worlds. */
  private abs(): TermNode {
    const at = this.cursor.here;
    this.cursor.advance();
    const typeParams = this.cursor.at("lbracket") ? this.typeBinders() : [];
    const params = this.funBinders("a parameter name");
    this.cursor.expect("arrow", "`->`, then the body");
    const body = this.blockOrExp("the function's body, indented past the `fn`");
    return { kind: "Abs", typeParams, params, body, at };
  }

  private match(): TermNode {
    const keyword = this.cursor.peek();
    this.cursor.advance();
    const scrutinee = this.exp(PREFIX + 1);
    this.cursor.expect("with", "`with`, then the arms");
    const arms = this.arms("arm", (at) => this.matchArm(at));
    return { kind: "Match", scrutinee, arms, at: keyword.at };
  }

  private matchArm(at: Position): MatchArm {
    const pattern = this.matchPat();
    this.cursor.expect("arrow", "`->`");
    // Past its `|`, not level with it: the arm list's items begin one column
    // right of the bar, so a body there is the next item rather than this one's.
    const body = this.blockOrExp("the arm's body, indented past its `|`");
    return { pattern, body, at };
  }

  /**
   * `_`, `C`, or `C(x, y)`. A name here is always a constructor and one inside
   * the parentheses always a binder, so a misspelt constructor cannot quietly
   * become a catch-all -- nor can one that fails to parse, the arm it heads
   * being dropped whole rather than left covering anything.
   */
  private matchPat(): MatchPat {
    // The one head position where `_` means something, so it is read as a
    // binder and the catch-all falls out of the wildcard case.
    const head = this.binderName("a constructor name or `_`");
    if (head.text === undefined) return { kind: "PWild", at: head.at };

    const name = { text: head.text, at: head.at };
    const args = this.cursor.at("lparen") ? this.plainFunBinders() : [];
    return { kind: "PCtor", name, args, at: head.at };
  }

  /** The postfix tier: application and instantiation, both left-associative. */
  private postfix(): TermNode {
    let term = this.atom();
    for (;;) {
      const open = this.cursor.peek();
      if (open.kind === "lparen") {
        term = { kind: "App", callee: term, args: this.funArgs(), at: open.at };
      } else if (open.kind === "lbracket") {
        term = {
          kind: "TypeApp",
          callee: term,
          args: this.typeArgs(),
          at: open.at,
        };
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
      const typeParams = this.typeBinders();
      const params = this.domainTypes();
      this.cursor.expect("arrow", "`->`, since a quantifier needs a function");
      return { kind: "FunType", typeParams, params, result: this.type(), at };
    }

    if (this.cursor.at("lparen")) {
      const params = this.domainTypes();
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
    const args = this.cursor.at("lbracket") ? this.typeArgs() : [];
    return { kind: "NameType", name, args, at };
  }

  /**
   * `(A, B)`, an arrow's left -- and a constructor's fields, which are that
   * arrow's left too, a constructor being an ordinary function.
   *
   * Neither binders nor arguments today, since a parameter names nothing a type
   * can mention. This is the rule dependent arrows would grow names in, and
   * where a constructor's fields would get them back with it.
   */
  private domainTypes(): TypeNode[] {
    this.cursor.expect("lparen", "`(`, a parameter list");
    return this.commaList("rparen", "`)`", true, () => this.domainType());
  }

  /**
   * One of them, and a word for the name that cannot yet precede it: `x: A`
   * here reads as the type `x` followed by wreckage, and `expected \`)\`` would
   * be a true thing to say about a line whose actual fault is elsewhere.
   */
  private domainType(): TypeNode {
    const type = this.type();
    if (this.cursor.at("colon")) {
      this.cursor.fail("`,` or `)`, since a parameter list holds types alone");
    }
    return type;
  }

  /**
   * The items of a bracketed list and the bracket that ends it. Not the opener:
   * every list rule below reads its own before coming here, so a rule that may
   * find no list at all tests for that bracket itself, which is what keeps the
   * optionality readable from the call site rather than hidden in a name.
   *
   * `allowEmpty` is the one thing the call sites disagree on: `()` is a call
   * with no arguments and `[]` a binder list binding nothing, but `f[]` and
   * `Pair[]` are neither, so those want the first item reported as missing here
   * rather than the emptiness noticed by an arity check much later.
   */
  private commaList<T>(
    close: TokenKind,
    closeWhat: string,
    allowEmpty: boolean,
    parse: () => T,
  ): T[] {
    const items: T[] = [];
    if (allowEmpty && this.cursor.at(close)) {
      this.cursor.advance();
      return items;
    }
    do items.push(parse()); while (this.cursor.accept("comma") !== undefined);
    this.cursor.expect(close, closeWhat);
    return items;
  }

  /**
   * `[A, B <: C]` -- the binding form, and one of the two things brackets ever
   * hold. Bounds are parallel: a bound may not name its own group.
   */
  private typeBinders(): TypeParam[] {
    this.cursor.expect("lbracket", "`[`, a type parameter list");
    return this.commaList("rbracket", "`]`", true, () => this.typeBinder());
  }

  private typeBinder(): TypeParam {
    const name = this.binderName("a type parameter");
    const bound = this.cursor.accept("subtype") === undefined
      ? undefined
      : this.type();
    return bound === undefined
      ? { name, at: name.at }
      : { name, bound, at: name.at };
  }

  /** `[A, B]` -- the instantiating form. At least one: `f[]` instantiates none. */
  private typeArgs(): TypeNode[] {
    this.cursor.expect("lbracket", "`[`, a type argument list");
    return this.commaList("rbracket", "`]`", false, () => this.type());
  }

  /**
   * `[A, B]`, names alone: a declaration's parameters are what its uses
   * instantiate, so there is no variable left for a bound to constrain.
   *
   * Read as binders and rejected after, rather than parsed by a rule of its
   * own. One bracket form covers both, and the report can be about the bound
   * itself -- pointing at it, saying why it has no meaning here -- where a rule
   * refusing to read it could only have named the `,` or `]` it wanted instead.
   */
  private plainTypeBinders(): BindingIdent[] {
    return this.typeBinders().map(({ name, bound }) => {
      if (bound !== undefined) {
        this.cursor.failAt(
          bound.at,
          "a declaration's type parameters take no bound",
        );
      }
      return name;
    });
  }

  /**
   * `(x: A, y)` -- the binding form, where an annotation is allowed and not
   * required. Its absence is not an omission to report here: the checker takes
   * the type from the expected type instead, and complains only if there is
   * none. Required of a `fn`, which has no form taking none.
   */
  private funBinders(what: string): Param[] {
    this.cursor.expect("lparen", "`(`, a parameter list");
    return this.commaList("rparen", "`)`", true, () => this.funBinder(what));
  }

  private funBinder(what: string): Param {
    const name = this.binderName(what);
    const annotation = this.cursor.accept("colon") === undefined
      ? undefined
      : this.type();
    return annotation === undefined
      ? { name, at: name.at }
      : { name, annotation, at: name.at };
  }

  /**
   * `(x, y)`, names alone: a pattern's binders take no annotation, the field's
   * type being settled by the declaration, and a pattern that restated it could
   * disagree with it.
   */
  private plainFunBinders(): BindingIdent[] {
    return this.funBinders("a name to bind").map(({ name, annotation }) => {
      if (annotation !== undefined) {
        this.cursor.failAt(
          annotation.at,
          "a pattern binds names alone, the field's type coming from the datatype",
        );
      }
      return name;
    });
  }

  /** `(a, b)` -- the applying form. Empty is a call of no arguments. */
  private funArgs(): TermNode[] {
    this.cursor.expect("lparen", "`(`, an argument list");
    return this.commaList("rparen", "`)`", true, () => this.exp(EXPR));
  }

  private ident(what: string): Ident {
    const token = this.cursor.expect("identifier", what);
    return { text: token.text, at: token.at };
  }

  /**
   * A name that has to be one: what a declaration or a constructor is called.
   *
   * Binding positions only. A `_` written where a type or a term is *used* is
   * left alone, resolving to nothing like any other unbound name -- calling
   * that a syntax error would say the wrong thing about a plain typo.
   */
  private declName(what: string): Ident {
    const name = this.ident(what);
    if (name.text === WILDCARD) this.cursor.failAt(name.at, what);
    this.refuseBang(name);
    return name;
  }

  /** The name at a binding occurrence, `_` meaning it declines to have one. */
  private binderName(what: string): BindingIdent {
    const token = this.cursor.expect("identifier", what);
    const text = token.text === WILDCARD ? undefined : token.text;
    const name = { text, at: token.at };
    this.refuseBang(name);
    return name;
  }

  /**
   * A trailing `!` marks a builtin, and only the checker names one. Refused
   * everywhere a name is *written to be resolved against* -- a binder, a
   * declaration, a constructor, the head of a pattern -- which leaves the one
   * position that matters: a use, so `set!(c, x)` is the point, and a use that
   * resolves to nothing is an unknown name like any other, which is what a
   * misspelt `st!` should be told.
   *
   * Here for the same reason `_`'s rule is here. Both are ordinary identifiers
   * to the lexer, so which positions admit them is a decision the parser makes
   * once, and nothing downstream compares against either again.
   */
  private refuseBang(name: BindingIdent | Ident): void {
    if (name.text === undefined || !name.text.endsWith(BANG)) return;
    this.cursor.failAt(
      name.at,
      `${name.text} may not be bound: a trailing \`${BANG}\` marks a builtin`,
    );
  }
}

/**
 * An ordinary identifier to the lexer, so which positions admit it is decided
 * here. Downstream sees an `BindingIdent` that either has a name or does not, and
 * no pass walking binders compares against this again.
 */
export const WILDCARD = "_";

/**
 * The suffix that marks a builtin operation. Lexically part of the name, so
 * this is what tells a use from a declaration of one -- see `refuseBang`.
 */
export const BANG = "!";

function wildcard(at: Position): BindingIdent {
  return { text: undefined, at };
}
