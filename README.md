# egraph — Wasm straight-line superoptimizer

Loop/jump-free WebAssembly basic blocks are optimized via backward residual-goal search and equality saturation.

## Architecture (two phases)

**Phase 1 — arithmetic rewrite synthesis** (`synthesis.rs`, `al/`, `value.rs`)

- Encode SpecTec AL semantics as Z3 constraints
- Enumerate value-level AST pairs and verify equivalence (random tests + Z3)
- Rules are value-level s-expressions, e.g. `(i32.div_u ?a 1) => (i32.mul ?a 1)`
- Cached in `rules-ast{N}.cache`

**Phase 2 — backward shortest instruction search** (`search.rs`, `inverse.rs`, `goal.rs`, `canon.rs`)

- Peel residual goals `G = (stack, locals)` from `fin` back to `init`
- Local slot `⋆` (don't-care) encodes register liveness
- Arithmetic alternatives branch via e-graph binop decompositions (Phase 1 rules)
- Normalized goals `⌈G⌉` are memoization keys
- Solvers: BFS, Greedy, A* (default)

## Usage

```sh
# Synthesize rules only (JSON to stdout)
cargo run --release -- --synthesize-only --max-ast-size 3

# Optimize a Wasm module (.wat or .wasm)
cargo run --release -- examples/example.wat

# A* with peel depth 16 (default)
cargo run --release -- examples/example.wat --solver astar --window 16

# List extracted segments without optimizing
cargo run --release -- examples/example.wat --segments-only
```

## Supported features

| Feature | Status |
|---------|--------|
| i32 binops (add/mul/div_u/div_s/shl) | yes |
| local.get / local.set / local.tee | yes |
| Backward peel + memoization + A* | yes |
| Wasm parse + straight-line segment extraction | yes |
| Optimized Wasm output | no |
| globals / linear memory | no |
| Loop/branch optimization (segment split only) | no |
| Inverse peel for `drop` | no |

## PoC limits

- Stack height ≤ 4 (`MAX_STACK_HEIGHT`)
- Local slots 0..=2 only
- i32 only
- Peel depth capped by `--window` (default 16)

## Source layout

- `src/goal.rs` — residual goals (stack + locals)
- `src/inverse.rs` — inverse peel rules
- `src/canon.rs` — e-graph normalization and binop branching
- `src/heuristic.rs` — admissible A* heuristics (`h_stack`, `h_local`, `h_node`, `h_dep`)
- `src/forward.rs` — forward symbolic execution
- `src/wasm/` — Wasm parsing and segment extraction
- `src/al/` — SpecTec AL semantics
- `src/example.rs` — loads `examples/example.wat` for tests and docs
- `examples/` — running example (`example.wat`) and SMT-LIB sample (`smt-lib.md`)

See also [encoding.md](encoding.md), [idea.md](idea.md), and [examples/README.md](examples/README.md).
