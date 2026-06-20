;; Optimal solution for examples/example.wat (idea.md §12).
;; init: stack=[], local{0:?L0}
;; fin:  stack=[(L0*2)*4, L0<<1], local{0:L0<<1}
(module
  (func (export "f") (param i32) (result i32 i32)
    local.get 0
    i32.const 3
    i32.shl
    local.get 0
    i32.const 1
    i32.shl
    local.tee 0
  )
)
