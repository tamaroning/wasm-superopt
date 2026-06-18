;; Running example from idea.md, intentionally bloated for the optimizer.
;; init: stack=[], local{0:?L0}
;; fin:  stack=[(L0+1)*4, L0+1], local{0:L0+1}
(module
  (func (export "f") (param i32) (result i32 i32)
    local.get 0
    i32.const 0
    i32.add
    i32.const 1
    i32.add
    local.tee 0
    i32.const 0
    i32.add
    i32.const 4
    i32.mul
    i32.const 0
    i32.add
    local.get 0
    i32.const 0
    i32.add
  )
)
