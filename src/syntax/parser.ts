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
  DefItem,
  DomainType,
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
import { QUALIFIER } from "./ast.ts";
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
    const items: BlockItem[] = [];
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
        items.push({ name: wildcard(last.at), bound: last, at: last.at });
        last = undefined;
      }

      const mark = this.cursor.mark();
      try {
        if (top && this.cursor.at("datatype")) {
          decls.push(this.datatypeDecl());
        } else if (top && this.cursor.at("typedef")) {
          decls.push(this.aliasDecl());
        } else if (this.cursor.at("let")) {
          items.push(this.letBinding());
        } else if (this.cursor.at("def")) {
          // Adjacent, so anything between two `def`s closes the group: a
          // `let` is sequential and a bare expression binds `_`, so either
          // would have to be in scope for a member above to recur with one
          // below. The run is the largest scope where that cannot be asked.
          const def = this.defBinding();
          const open = items.at(-1);
          if (open !== undefined && Array.isArray(open)) open.push(def);
          else items.push([def]);
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

    // Each item is its node short of a body, which the fold supplies.
    return items.reduceRight<TermNode>(
      (body, item) =>
        Array.isArray(item)
          ? { kind: "LetRec", defs: item, body, at: item[0].at }
          : { kind: "Let", ...item, body },
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

  /** `datatype Pair[A, B] <: Base where` then its constructor arms. */
  private datatypeDecl(): DatatypeDecl {
    const keyword = this.cursor.peek(); // the `datatype` the block loop saw
    this.cursor.advance();
    const name = this.declName("a type name");

    const typeParams = this.cursor.at("lbracket")
      ? this.plainTypeBinders()
      : [];
    // A whole type and not a name with arguments, so an alias may stand here;
    // what it has to *be* is elaboration's question, which is where the table
    // saying so lives.
    const base = this.cursor.accept("subtype") === undefined
      ? undefined
      : this.type();
    // A pure delimiter: nothing but constructors may follow it, which is what
    // lets layout open their block wherever it sits.
    this.cursor.expect("where", "`where`, then the constructors");
    const ctors = this.arms("constructor", (at) => this.ctorDecl(at));
    return {
      kind: "DatatypeDecl",
      name,
      typeParams,
      ctors,
      at: keyword.at,
      ...(base === undefined ? {} : { base }),
    };
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
    // A constructor is an ordinary function, so its fields are a domain --
    // absent, and not empty, where none is written: `C()` is the nullary
    // function and `C` the value, which is a different declaration.
    const params = this.cursor.at("lparen") ? this.domainTypes() : undefined;
    const coercion = this.cursor.accept("arrow") === undefined
      ? undefined
      : this.coercion();
    return {
      name,
      at,
      ...(params === undefined ? {} : { params }),
      ...(coercion === undefined ? {} : { coercion }),
    };
  }

  /**
   * `-> Cons(x, r)`, after a constructor's fields. An ordinary term, read the
   * way an arm's body is; which of its positions have to be constructors of
   * the base is `resolveCoercionTails`, not a shape this rule can insist on.
   */
  private coercion(): TermNode {
    return this.blockOrExp("the coercion, indented past its `|`");
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
   * `def f(x: A)(y: B) : R = e`, without the separator or what follows it.
   *
   * Parameter lists and a result type are all a `def` adds to a `let`, and both
   * fold away here: the lists into the `Abs`, the result type into the
   * `FunType` that becomes the annotation. Whether there is an annotation is
   * then the only question left, and it decides whether the group sees this
   * member before its body is checked.
   */
  private defBinding(): DefItem {
    const at = this.cursor.here; // the `def` the block loop saw
    this.cursor.advance();
    const name = this.binderName("a name to bind");
    // Said here rather than left to `funBinders`, whose `(` is the right answer
    // to a missing list and the wrong one to a binding that wanted no list.
    if (this.cursor.at("equals") || this.cursor.at("colon")) {
      this.cursor.fail("a parameter list -- `let` is what binds a value");
    }
    const groups = this.paramGroups();
    const result = this.cursor.accept("colon") === undefined
      ? undefined
      : this.type();
    this.cursor.expect("equals", "`=`");
    const body = this.blockOrExp("the def's body, indented past the `def`");

    // A result type settles where the parameter types live, which settles the
    // rest. With one they live in the signature and nowhere else -- on the
    // `Abs` too they would be elaborated once for the entry the group reads and
    // once for the body, doubling every diagnostic they raise. Without one the
    // `Abs` is their only home, so an omitted type stands there.
    return result === undefined
      ? { name, bound: foldAbs(groups, body, at, ensureParamTypes), at }
      : {
        name,
        annotation: foldFunType(groups, result),
        bound: foldAbs(groups, body, at, dropWrittenTypes),
        at,
      };
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

  /**
   * `fn (x: A) -> e`, or `fn [T <: A](x: T)(y: B) -> e` -- one binder, both
   * worlds, and as many lists as are written.
   */
  private abs(): TermNode {
    const at = this.cursor.here;
    this.cursor.advance();
    const groups = this.paramGroups();
    this.cursor.expect("arrow", "`->`, then the body");
    const body = this.blockOrExp("the function's body, indented past the `fn`");
    return foldAbs(groups, body, at);
  }

  /**
   * One or more `[T](x: A)` groups, the optional type list belonging to the
   * value list that follows it.
   *
   * A group is where a batch of type arguments is solved, so writing two is how
   * an author says an argument must settle before a later one is looked at --
   * `foldr(xs)(z)(op)`, and Scala's `foldLeft(z)(op)` for the same reason. The
   * first is parsed unconditionally so a `fn` with no list fails where it
   * always did.
   */
  private paramGroups(): [ParamGroup, ...ParamGroup[]] {
    const groups: ParamGroup[] = [];
    do {
      const at = this.cursor.here;
      const typeParams = this.cursor.at("lbracket") ? this.typeBinders() : [];
      const params = this.funBinders("a parameter name");
      groups.push({ typeParams, params, at });
    } while (this.cursor.at("lbracket") || this.cursor.at("lparen"));
    // At least one, which is the whole of why a `def`'s bound is an `Abs`.
    return groups as [ParamGroup, ...ParamGroup[]];
  }

  private match(): TermNode {
    const keyword = this.cursor.peek();
    this.cursor.advance();
    const scrutinee = this.exp(PREFIX + 1);
    // `as List`, saying which datatype the patterns are of. Optional, the
    // checker filling it from the scrutinee's type -- so this is for a program
    // meant to be run without being checked, and for saying it on purpose.
    const datatype = this.cursor.accept("as") === undefined
      ? undefined
      : this.declName("the datatype the patterns are of").text;
    this.cursor.expect("with", "`with`, then the arms");
    const arms = this.arms("arm", (at) => this.matchArm(at));
    return {
      kind: "Match",
      scrutinee,
      arms,
      at: keyword.at,
      ...(datatype === undefined ? {} : { datatype }),
    };
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
      // Not an arrow, so it was a parenthesised type -- and only one fits,
      // unnamed: a name belongs to a parameter, so what carried one was a
      // parameter list whatever it holds.
      const only = params[0];
      if (
        params.length === 1 && only?.name === undefined && only !== undefined
      ) {
        return only.type;
      }
      this.cursor.fail("`->`, since a parameter list is not a type");
    }

    const atom = this.atomType();
    if (this.cursor.accept("arrow") === undefined) return atom;
    return {
      kind: "FunType",
      typeParams: [],
      params: [{ type: atom, at: atom.at }],
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
  private domainTypes(): DomainType[] {
    this.cursor.expect("lparen", "`(`, a parameter list");
    return this.commaList("rparen", "`)`", true, () => this.domainType());
  }

  /**
   * One of them, and a word for the name that cannot yet precede it: `x: A`
   * here reads as the type `x` followed by wreckage, and `expected \`)\`` would
   * be a true thing to say about a line whose actual fault is elsewhere.
   */
  /**
   * `A`, or `x: A`. The name is optional and means nothing yet -- see
   * `DomainType`.
   *
   * Read as a type first and reinterpreted on the `:`, which is what saves a
   * second token of lookahead: only a bare name can be one, and a bare name is
   * a `NameType` with no arguments. So `Pair[A]: B` is refused here rather than
   * parsed into something no rule would know what to do with.
   */
  private domainType(): DomainType {
    const at = this.cursor.here;
    const type = this.type();
    if (this.cursor.accept("colon") === undefined) return { type, at };
    if (type.kind !== "NameType" || type.args.length > 0) {
      this.cursor.failAt(
        at,
        "only a name may be given a type in a parameter list",
      );
    }
    return { name: this.toBinder(type.name), type: this.type(), at };
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
    this.requirePlainName(name);
    return name;
  }

  /** The name at a binding occurrence, `_` meaning it declines to have one. */
  private binderName(what: string): BindingIdent {
    return this.toBinder(this.ident(what));
  }

  /**
   * An `Ident` at a position that binds, under the two rules every such
   * position obeys: `_` names nothing, and a trailing `!` is refused. Split out
   * because a domain's name is read as a type and only then found to be a
   * binder -- the rules are the same wherever the name came from.
   */
  private toBinder(name: Ident): BindingIdent {
    const bound = {
      text: name.text === WILDCARD ? undefined : name.text,
      at: name.at,
    };
    this.requirePlainName(bound);
    return bound;
  }

  /**
   * A position that *binds* takes a plain name. Two spellings are refused
   * here, and for one reason: each names something only the checker seeds, so
   * writing one at a binder would be redeclaring a name its owner already
   * holds. A trailing `!` marks a builtin; an interior `.` qualifies a
   * constructor by its datatype, and `List.Cons` belongs to the declaration of
   * `List` and to nothing an author writes.
   *
   * Which leaves the position that matters, a *use*: `set!(c, x)` is the
   * point, and so is `List.Cons(x, xs)`. A use resolving to nothing is an
   * unknown name like any other, which is what a misspelt `st!` or
   * `Lst.Cons` should be told.
   *
   * Here for the same reason `_`'s rule is here. All three are ordinary
   * identifiers to the lexer, so which positions admit them is a decision the
   * parser makes once, and nothing downstream compares against any of them
   * again.
   */
  private requirePlainName(name: BindingIdent | Ident): void {
    const text = name.text;
    if (text === undefined) return;
    if (text.endsWith(BANG)) {
      this.cursor.failAt(
        name.at,
        `${text} may not be bound: a trailing \`${BANG}\` marks a builtin`,
      );
    }
    if (text.includes(QUALIFIER)) {
      this.cursor.failAt(
        name.at,
        `${text} may not be bound: a \`${QUALIFIER}\` names a ` +
          `constructor of a datatype`,
      );
    }
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
 * this is what tells a use from a declaration of one -- see
 * `requirePlainName`.
 */
export const BANG = "!";

function wildcard(at: Position): BindingIdent {
  return { text: undefined, at };
}

/**
 * What a block collects: one sequential binding, or a run of `def`s that see
 * each other, told apart by being an array. Non-empty, so the run's position is
 * its first member's and is recorded nowhere else.
 */
type BlockItem = LetItem | [DefItem, ...DefItem[]];

/** One `[T](x: A)` list pair, before it is folded into an arrow. */
type ParamGroup = {
  readonly typeParams: readonly TypeParam[];
  readonly params: readonly Param[];
  readonly at: Position;
};

/**
 * `[T](x: A)(y: B) e` as nested `Abs`, which is what it means. Currying gives
 * staging for free, so several lists need no term form and no function type of
 * their own -- the sugar is gone before anything downstream sees it.
 *
 * The outermost keeps the keyword's own position, every inner one its list's,
 * so a diagnostic about the function lands on `fn` or `def` and one about a
 * later list lands on the list. `rewrite` is where a `def` says which of the
 * two places its types are written; a `fn` writes them here and leaves it.
 */
function foldAbs(
  groups: readonly [ParamGroup, ...ParamGroup[]],
  body: TermNode,
  at: Position,
  rewrite: (group: ParamGroup) => ParamGroup = (group) => group,
): Extract<TermNode, { kind: "Abs" }> {
  const layer = (group: ParamGroup, inner: TermNode, at: Position) => {
    const { typeParams, params } = rewrite(group);
    return { kind: "Abs", typeParams, params, body: inner, at } as const;
  };

  let folded: TermNode = body;
  for (let i = groups.length - 1; i >= 1; i -= 1) {
    const group = groups[i];
    if (group === undefined) continue;
    folded = layer(group, folded, group.at);
  }
  return layer(groups[0], folded, at);
}

/** The type a parameter was given, or the node standing for the one it wasn't. */
function ensureParamType(param: Param): TypeNode {
  return param.annotation ??
    { kind: "MissingParamType", name: param.name, at: param.name.at };
}

/**
 * One type per parameter, so what reads the `Abs` has no case for the absence.
 * The omission stands in the tree rather than being reported here, a parser
 * error withholding the whole tree and so costing the file its type checking
 * over one binder.
 */
function ensureParamTypes(group: ParamGroup): ParamGroup {
  return {
    ...group,
    params: group.params.map((param) => ({
      ...param,
      annotation: ensureParamType(param),
    })),
  };
}

/**
 * Drop what the signature already carries -- bounds as well as parameter types,
 * both read twice otherwise. Types alone, never a binder or a position, so what
 * a diagnostic points at is unchanged and only where it was read from moves.
 *
 * Reaching further than `ensureParamTypes` on purpose: there is no missing
 * bound to ensure, one left off meaning `unknown` rather than nothing at all.
 */
function dropWrittenTypes(group: ParamGroup): ParamGroup {
  return {
    ...group,
    typeParams: group.typeParams.map(({ name, at }) => ({ name, at })),
    params: group.params.map(({ name, at }) => ({ name, at })),
  };
}

/**
 * `foldAbs` against the other target: the lists go once into nested `Abs`s and
 * once into the `FunType` that is the signature, agreeing because one list
 * feeds both.
 */
function foldFunType(
  groups: readonly ParamGroup[],
  result: TypeNode,
): TypeNode {
  let type = result;
  for (let i = groups.length - 1; i >= 0; i -= 1) {
    const group = groups[i];
    if (group === undefined) continue;
    type = {
      kind: "FunType",
      typeParams: group.typeParams,
      params: group.params.map((param) => ({
        name: param.name,
        type: ensureParamType(param),
        at: param.at,
      })),
      result: type,
      at: group.at,
    };
  }
  return type;
}
