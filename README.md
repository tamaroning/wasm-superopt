# WebAssembly Superoptimizer

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
# Optimize a Wasm module (.wat or .wasm)
cargo run --release -- examples/example.wat
```
