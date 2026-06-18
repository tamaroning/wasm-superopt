# SpecTec->Superoptimizer PoC

1. Encode SpecTec AL into SMT constraints
2. Generate rewriting rules (LHS->RHS) by exhaustive enumeration and equivalence check (with Z3).
3. Optimize i32 value expressions by applying the rules with equality saturation.

Rewriting rules are **value-level** s-expressions (no `stack.slot` wrapper), e.g.
`(i32.div_u ?a 1) => (i32.mul ?a 1)`. They match subexpressions anywhere in a value DAG.

```sh
cargo run --release -- --synthesize-only --max-seq-len 2
```

- src/
    - sema/
        - defs.rs: Generated from SpecTec AL.
        - spec.rs: Mapping instructions to reduction rules in AL.
    - value.rs: Pure i32 value DAG (`ValueLang`) for equality saturation.


Supported ops
- [x] Binary ops (value-level rules)
- [ ] Locals
- [ ] Globals
- [ ] Memory access
- [ ] Polymorphic ops (select, drop, etc.)

Semantic equivalence
- [x] Stack
- [x] Trap
- [ ] Locals
- [ ] Globals
- [ ] Memory
