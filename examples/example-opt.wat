;; init: stack=[], local{0:?L0}
;; fin:  stack=[(L0*2)*4, L0<<1], local{0:L0<<1}
(module
  (global (mut i32) (i32.const 0))

  (func (export "f") (param i32)
    ;; target starts here
    local.get 0
    i32.const 1
    i32.shl
    local.tee 0
    local.get 0
    i32.const 2
    i32.shl
    ;; target ends here
    global.set 0
  )
)
