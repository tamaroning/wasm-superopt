# SpecTec->Superoptimizer PoC

1. Encode SpecTec AL into SMT constraints
2. Generate rewriting rules (LHS->RHS) by exhaustive enumeration and equivalene check (with Z3).
3. Optimize a given program by applying the rules with equality saturation.

```sh
cargo run --release -- --synthesize-only --max-seq-len 2
```

- [x] Binary ops
- [x] Trap
- [ ] Locals
- [ ] Globals
