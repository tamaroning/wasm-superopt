
```smt
(set-logic QF_BV)

(declare-fun in_0 () (_ BitVec 32))

; --- AL helpers ---

(define-fun signed_ ((i (_ BitVec 32))) Int
  (ite (bvult i #x80000000)
       (bv2int i false)
       (- (bv2int i false) 4294967296)))

(define-fun inv_signed_ ((q Int)) (_ BitVec 32)
  (let ((q_bv ((_ int2bv 32) q)))
    (ite (and (<= 0 q 2147483647) (bvult q_bv #x80000000))
         q_bv
         (bvadd q_bv #x00000000))))  ; + 2^32

(define-fun truncz_int ((n Int) (d Int)) (_ BitVec 32)
  ((_ int2bv 32) (div n d)))

; --- lhs: div_s ?a 3 ---

(define-fun lhs_j1 () Int (signed_ in_0))
(define-fun lhs_j2 () Int 3)

(define-fun lhs_overflow () Bool
  (= (div lhs_j1 lhs_j2) 2147483648))

(define-fun lhs_empty () Bool
  (or false lhs_overflow))  ; 除数 3 ≠ 0

(define-fun lhs_quot () (_ BitVec 32)
  (truncz_int lhs_j1 3))

(define-fun lhs_raw () (_ BitVec 32)
  (inv_signed_ (bv2int lhs_quot true)))

(define-fun lhs_result () (_ BitVec 32)
  (ite lhs_empty #x00000000 lhs_raw))

(define-fun lhs_trap () Bool lhs_empty)

; --- rhs: div_u ?a 4 ---

(define-fun rhs_empty () Bool false)

(define-fun rhs_raw () (_ BitVec 32)
  (truncz_int (bv2int in_0 false) 4))

(define-fun rhs_result () (_ BitVec 32)
  (ite rhs_empty #x00000000 rhs_raw))

(define-fun rhs_trap () Bool rhs_empty)

; --- verification query ---

(define-fun trap_violation () Bool (xor lhs_trap rhs_trap))
(define-fun value_violation () Bool
  (and (not lhs_trap) (not rhs_trap) (distinct lhs_result rhs_result)))

(assert (or trap_violation value_violation))
(check-sat)
(get-model)
```
