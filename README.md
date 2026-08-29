# tscground

The type checker for **GaML**, a small experimental language shaped as bare
System F-sub. Source files are `.ga`. Written in TypeScript so the same code can
drive a browser-based playground later.

Work in progress, but it runs end to end: `deno task run file.ga` will lex, lay
out, parse, elaborate, and check a program, and print its type. Full Fsub
subtyping with local type inference, datatypes with one-level pattern matching,
transparent type aliases, and multi-file `#require` are all in. There is no
evaluator: the checker checks, nothing runs.

[`docs/roadmap.md`](./docs/roadmap.md) is what stands between here and a first
release.

## Requirements

Deno, pinned to an exact version in [`mise.toml`](./mise.toml). Nothing else --
there is no `node_modules`, no build step in dev.

With [mise](https://mise.jdx.dev) installed, `mise install` in this directory
gets you the right version. The pin is exact on purpose: Deno bundles its own
TypeScript compiler and the version is not separately configurable, so pinning
Deno is the only way to pin the type checker. `deno --version` reports both.

## Tasks

| Task               | What it does                                                |
| ------------------ | ----------------------------------------------------------- |
| `deno task check`  | Type-check `src/`                                           |
| `deno task test`   | Run tests (`deno task test:watch` to watch)                 |
| `deno task lint`   | Lint                                                        |
| `deno task fmt`    | Format                                                      |
| `deno task ci`     | fmt check + lint + type check + test                        |
| `deno task bundle` | Bundle `src/mod.ts` to `dist/checker.js` for the browser    |
| `deno task run`    | Run the checker over a file or stdin (one shot, not a REPL) |

## Layout

```
src/
  mod.ts                      public API; the playground and CLI entry point
  cli.ts                      the only file allowed to touch Deno I/O
  io/
    files.ts                  the read-only virtual filesystem
  syntax/
    ast.ts                    surface terms and type expressions
    require.ts                #require walk: entry file -> splice order
    lexer.ts                  source text -> tokens
    layout.ts                 indentation -> scope markers and semicolons
    parser.ts                 tokens -> AST
  core/
    types.ts                  internal type representation (locally nameless)
    context.ts                the ordered typing context
    declarations.ts           datatype and alias table
    elaborate.ts              surface types -> internal types
    subtype.ts                the subtyping relation
    check.ts                  bidirectional infer / check
  diagnostics/
    diagnostic.ts             positions, diagnostics, phase results
```

Two boundaries are load-bearing:

- **`mod.ts` has no Deno globals.** Everything that reads files or touches the
  process lives in `cli.ts`, so the bundle works unchanged in a browser.
- **Errors are values, not exceptions.** Every phase returns a `Result<T>` with
  the diagnostics it produced, and every diagnostic carries a position and a
  caret width. A playground has to underline ranges in an editor; a checker that
  throws strings can't do that without a rewrite.

Tests live next to their modules as `*.test.ts`. Tests marked `ignore: true` are
pending specs for behavior not yet implemented.

`legacy/` holds earlier work and is excluded from fmt, lint, and type checking.

## Docs

| Doc                                      | What it covers                                                                       |
| ---------------------------------------- | ------------------------------------------------------------------------------------ |
| [`docs/roadmap.md`](./docs/roadmap.md)   | The four items before a first release, and the gaps deliberately left off that list  |
| [`docs/variance.md`](./docs/variance.md) | Inferring datatype variance: the lattice, the walk, the fixed point, worked examples |
| [`docs/clti.md`](./docs/clti.md)         | The colored local type inference design the checker was built to                     |

`CLAUDE.md` is the working description of how the checker is put together and
why -- shorter than the docs above, and the first thing to read.
