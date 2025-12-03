export class Token
{
  readonly cat: string;
  readonly text: string;
  readonly ln: number;
  readonly col: number;

  constructor(cat: string, text: string, ln: number, col: number)
  {
    this.cat = cat; this.text = text; this.ln = ln; this.col = col;
  }
}


class IterLines
{
  idx = -1;

  get proc()
  {
    let self = this;
    return function* (ln: string)
    {
      self.idx++;
      if (ln.trim().length > 0)
        yield new Token("", ln, self.idx, 0);
    };
  }
}


function calcIndent()
{
  let hist = [0];

  return function* (lineData: Token)
  {
    let { text: ln, ln: idx } = lineData;
    let whites = ln.match(/ */)![0];
    if (whites.length > hist.at(-1)!)
    {
      hist.push(whites.length);
      yield new Token("indent", whites, idx, 0);
    }
    else
    {
      while (whites.length < hist.at(-1)!)
      {
        hist.pop();
        yield new Token("dedent", whites, idx, 0);
      }
      if (whites.length > hist.at(-1)!)
      {
        throw new Error(`Fatal: unexpected indent\n${idx}|${ln}`);
      }
    }
    yield new Token("", ln, idx, whites.length);
  };
}


function tokenize()
{
  let toks: [string, RegExp][] =
    [
      ["key", /let\b|ref\b|type\b/],
      ["num", /\d+\b/],
      ["id", /[_a-zA-Z][_a-zA-Z0-9!?]*/],
      ["op", /[-+*/!]|:?=/],
      ["delim", /->|<:|[\[\](){}:;\\]/],
      ["white", /\s+/],
      ["comment", /#.*/],
    ];
  let re = new RegExp(toks.map(([cat, pat]) =>
    `(?<${cat}>${pat.source})`).join("|"), "y");

  return function* (data: Token)
  {
    if (data.cat.length > 0)
    {
      yield data;
    }
    else
    {
      re.lastIndex = data.col;
      while (re.lastIndex < data.text.length)
      {
        let col = re.lastIndex;
        let match = re.exec(data.text);
        if (match == null)
        {
          let text = data.text.substring(col);
          throw new Error(`Fatal: unknown token\n${data.ln}|${text}`);
        }
        let kv = match.groups!;
        for (let [cat, text] of Object.entries(kv))
        {
          if (text == null || ["white", "comment"].includes(cat)) continue;
          yield new Token(cat, text, data.ln, col);
        }
      }
    }
  };
}


export class Tokenizer
{
  private readonly stream: AsyncGenerator<Token, Token>;

  constructor(reader: AsyncGenerator<string>)
  {
    let iterlines = new IterLines();
    let calcIndent_ = calcIndent();
    let tokenize_ = tokenize();
    this.stream = (async function* ()
    {
      for await (let ln of reader)
      {
        yield* iterlines.proc(ln).flatMap(tokenize_);
      }
      return new Token("eof", "", iterlines.idx + 1, 0);
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

  async requireToken(cond: string | { cat: string; text?: string; }): Promise<Token>
  {
    let res = await this.getToken();
    let msg = `Syntax Error (${res.ln}, ${res.col}): ${res.text} <${res.cat}>`;
    if (typeof cond === "string" &&
      !(res.text == cond && res.cat != "eof"))
    {
      throw new Error(`${msg}\nExpect ${cond}`);
    }
    else if (typeof cond === 'object' &&
      !(cond.cat == res.cat && (cond.text == null || cond.text == res.text)))
    {
      throw new Error(`${msg}\nExpect ${cond.text ?? ""} <${cond.cat}>`);

    }
    return res;
  }
};