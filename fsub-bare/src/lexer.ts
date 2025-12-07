import { Pos, syntaxError } from "./defs";

export type Token = { cat: string; text: string; pos: Pos; };


class IterLines
{
  idx = -1;

  get proc()
  {
    let self = this;
    return function* (ln: string): Generator<Token>
    {
      self.idx++;
      if (ln.trim().length > 0)
        yield { cat: "", text: ln, pos: [self.idx, 0] };
    };
  }
}


function calcIndent()
{
  let hist = [0];

  return function* (lineData: Token): Generator<Token>
  {
    let { text: ln, pos: [idx] } = lineData;
    let whites = ln.match(/ */)![0];
    if (whites.length > hist.at(-1)!)
    {
      hist.push(whites.length);
      yield { cat: "indent", text: whites, pos: [idx, 0] };
    }
    else
    {
      while (whites.length < hist.at(-1)!)
      {
        hist.pop();
        yield { cat: "dedent", text: whites, pos: [idx, 0] };
      }
      if (whites.length > hist.at(-1)!)
        throw syntaxError([idx, 0], `unexpected indent\n\t${ln}`);
    }
    yield { cat: "", text: ln, pos: [idx, whites.length] };
  };
}


function tokenize()
{
  let toks: [string, RegExp][] =
    [
      ["key", /let\b|ref\b/],
      ["prim", /Int\b|Unit\b|Ref\b|Any\b/],
      ["num", /\d+\b/],
      ["id", /[_a-zA-Z][_a-zA-Z0-9!?]*/],
      ["op2", /->|<:|:=/],
      ["op1", /[-+*/=!\[\](){}:;\\]/],
      ["white", /\s+/],
      ["comment", /#.*/],
    ];
  let re = new RegExp(toks.map(([cat, pat]) =>
    `(?<${cat}>${pat.source})`).join("|"), "y");

  return function* (data: Token): Generator<Token>
  {
    if (data.cat.length > 0)
    {
      yield data;
    }
    else
    {
      let [ln, col] = data.pos;
      re.lastIndex = col;
      while (re.lastIndex < data.text.length)
      {
        let col = re.lastIndex;
        let match = re.exec(data.text);
        if (match == null)
        {
          let text = data.text.substring(col);
          throw syntaxError([ln, col], `unknown token\n\t${text}`);
        }
        let kv = match.groups!;
        for (let [cat, text] of Object.entries(kv))
        {
          if (text == null || ["white", "comment"].includes(cat)) continue;
          yield { cat, text, pos: [ln, col] };
        }
      }
    }
  };
}


type TokenSpec =
  | string
  | string[]
  | { cat: string, text?: string; };

function checkTokenSpec(tok: Token, spec: TokenSpec): boolean
{
  if (typeof spec === "string")
    return tok.text === spec;
  if (Array.isArray(spec))
    return spec.includes(tok.text);
  return tok.cat == spec.cat && tok.text == (spec.text ?? tok.text);
}

function formatTokenSpec(spec: TokenSpec): string
{
  if (typeof spec === "string" || Array.isArray(spec))
    return `${spec}`;
  return `${spec.text ?? ""} <${spec.cat}>`;
}


export class Tokenizer
{
  private readonly stream: AsyncGenerator<Token, Token>;

  constructor(reader: AsyncGenerator<string>)
  {
    let iterlines = new IterLines();
    let tokenize_ = tokenize();
    this.stream = (async function* ()
    {
      for await (let ln of reader)
      {
        yield* iterlines.proc(ln).flatMap(tokenize_);
      }
      return { cat: "eof", text: "", pos: [iterlines.idx + 1, 0] };
    })();
  }

  private peek: Token | undefined;

  async peekToken(): Promise<Token>
  {
    if (this.peek == null)
    {
      this.peek = (await this.stream.next()).value;
    }
    return this.peek;
  }

  async getToken(): Promise<Token>
  {
    let res: Token;
    if (this.peek == null)
    {
      res = (await this.stream.next()).value;
    }
    else
    {
      res = this.peek;
      this.peek = undefined;
    }
    return res;
  }

  async requireToken(cond: TokenSpec): Promise<Token>
  {
    let res = await this.getToken();
    if (!checkTokenSpec(res, cond))
      throw syntaxError(res.pos,
        `expect ${formatTokenSpec(cond)}, got ${res.text} <${res.cat}>`);
    return res;
  }

  async unexpectedToken(cond: TokenSpec): Promise<never>
  {
    let res = await this.getToken();
    throw syntaxError(res.pos,
      `expect ${formatTokenSpec(cond)}, got ${res.text} <${res.cat}>`);
  }

  async tryGetToken(spec: TokenSpec): Promise<Token | undefined>
  {
    let tok = await this.peekToken();
    if (checkTokenSpec(tok, spec))
      return await this.getToken();
    return undefined;
  }
};