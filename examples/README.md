# Examples

## `example.wat` — running optimizer example (idea.md §12)

Bloated straight-line function the superoptimizer shortens.

- **init:** `stack=[]`, `local{0:?L0}`
- **fin:** `stack=[(L0*2)*4, L0<<1]`, `local{0:L0<<1}`
- **expected optimum:** 7 instructions (see `example-opt.wat`)

```sh
cargo run --release -- examples/example.wat
# or: cargo run --release -- examples/example.wasm
```

Prebuilt binaries: `example.wasm`, `example-opt.wasm`. Regenerate from WAT:

```sh
wat2wasm examples/example.wat -o examples/example.wasm
wat2wasm examples/example-opt.wat -o examples/example-opt.wasm
```

`src/example.rs` loads the bloated segment for optimization demos and derives canonical `init`/`fin` from `example.wat` / `example-opt.wat`.

## `example-opt.wat` / `example-opt.wasm` — optimal solution (7 instructions)

Reference implementation: `tee` stores `L0<<1` while leaving stack `[(L0*2)*4, L0<<1]`.

## `smt-lib.md` — human-readable SMT-LIB sample

Illustrates how a rule equivalence query looks after AL → Z3 encoding. See [encoding.md](../encoding.md).
