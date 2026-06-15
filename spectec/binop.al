;; i32.div_s (binary opcode 0x6D)
;;   instruction: BINOP I32 (DIV S)
;;   instantiation: Step_pure/binop(I32, DIV S)

Step_pure/binop nt binop {
 Assert (top_value(nt))
 Pop (numtype_0.CONST c_2)
 Assert (top_value(num))
 Pop (numtype_0.CONST c_1)
 If ((|$binop_(nt, binop, c_1, c_2)| <= 0)) {
   Trap
 }
 Let c = choose($binop_(nt, binop, c_1, c_2))
 Push (nt.CONST c)
}

size valtype {
 If ((valtype = I32)) {
   Return 32
 }
 If ((valtype = I64)) {
   Return 64
 }
 If ((valtype = F32)) {
   Return 32
 }
 If ((valtype = F64)) {
   Return 64
 }
 If ((valtype = V128)) {
   Return 128
 }
 Fail
}

sizenn nt {
 Return $size(nt)
}

;; $signed_ (3-numerics.spectec lines 20-22)
signed_ N i {
 If ((i < (2 ^ $nat$(($int$(N) - $int$(1)))))) {
   Return $int$(i)
 }
 Assert (((2 ^ $nat$(($int$(N) - $int$(1)))) <= i))
 Assert ((i < (2 ^ N)))
 Return ($int$(i) - $int$((2 ^ N)))
}

;; $inv_signed_ (3-numerics.spectec lines 24-26)
inv_signed_ N i {
 If ((($int$(0) <= i) /\ (i < $int$((2 ^ $nat$(($int$(N) - $int$(1)))))))) {
   Return $nat$(i)
 }
 Assert ((-($int$((2 ^ $nat$(($int$(N) - $int$(1)))))) <= i))
 Assert ((i < $int$(0)))
 Return $nat$((i + $int$((2 ^ N))))
}

list_ X X?{X <- X} {
 If (~(X?{X <- X} != None)) {
   Return []
 }
 Let ?(w) = X?{X <- X}
 Return [w]
}

iadd_ N i_1 i_2 {
 Return ((i_1 + i_2) \ (2 ^ N))
}

isub_ N i_1 i_2 {
 Return $nat$((($int$(((2 ^ N) + i_1)) - $int$(i_2)) \ $int$((2 ^ N))))
}

imul_ N i_1 i_2 {
 Return ((i_1 * i_2) \ (2 ^ N))
}

;; $idiv_ (3-numerics.spectec lines 108, 145-149)
idiv_ N sx i_1 i_2 {
 ;; def $idiv_(N, U, i_1, 0) = eps
 If ((sx = U)) {
   If ((i_2 = 0)) {
     Return ?()
   }
   ;; def $idiv_(N, U, i_1, i_2) = $truncz($(i_1 / i_2))
   Return ?($nat$($truncz(($rat$(i_1) / $rat$(i_2)))))
 }
 Assert ((sx = S))
 ;; def $idiv_(N, S, i_1, 0) = eps
 If ((i_2 = 0)) {
   Return ?()
 }
 ;; def $idiv_(N, S, i_1, i_2) = eps  -- if ... = $rat$(2^(N-1))
 If ((($rat$($signed_(N, i_1)) / $rat$($signed_(N, i_2))) = $rat$((2 ^ $nat$(($int$(N) - $int$(1))))))) {
   Return ?()
 }
 ;; def $idiv_(N, S, i_1, i_2) = $inv_signed_(N, $truncz(...))
 Return ?($inv_signed_(N, $truncz(($rat$($signed_(N, i_1)) / $rat$($signed_(N, i_2))))))
}

irem_ N sx i_1 i_2 {
 If ((sx = U)) {
   If ((i_2 = 0)) {
     Return ?()
   }
   Return ?($nat$(($int$(i_1) - $int$((i_2 * $nat$($truncz(($rat$(i_1) / $rat$(i_2)))))))))
 }
 Assert ((sx = S))
 If ((i_2 = 0)) {
   Return ?()
 }
 Let j_1 = $signed_(N, i_1)
 Let j_2 = $signed_(N, i_2)
 Return ?($inv_signed_(N, (j_1 - (j_2 * $truncz(($rat$(j_1) / $rat$(j_2)))))))
}

binop_ numtype binop_ iN_1 iN_2 {
 If (type(numtype) == Inn) {
   If ((binop_ = ADD)) {
     Return [$iadd_($sizenn(numtype), iN_1, iN_2)]
   }
   If ((binop_ = SUB)) {
     Return [$isub_($sizenn(numtype), iN_1, iN_2)]
   }
   If ((binop_ = MUL)) {
     Return [$imul_($sizenn(numtype), iN_1, iN_2)]
   }
   ;; def $binop_(Inn, DIV sx, iN_1, iN_2) = $list_(num_(Inn), $idiv_(...))
   If (case(binop_) == DIV) {
     Let (DIV sx) = binop_
     Return $list_(num_((Inn : Inn <: numtype)), $idiv_($sizenn(numtype), sx, iN_1, iN_2))
   }
   If (case(binop_) == REM) {
     Let (REM sx) = binop_
     Return $list_(num_((Inn : Inn <: numtype)), $irem_($sizenn(numtype), sx, iN_1, iN_2))
   }
   If ((binop_ = AND)) {
     Return [$iand_($sizenn(numtype), iN_1, iN_2)]
   }
   If ((binop_ = OR)) {
     Return [$ior_($sizenn(numtype), iN_1, iN_2)]
   }
   If ((binop_ = XOR)) {
     Return [$ixor_($sizenn(numtype), iN_1, iN_2)]
   }
   If ((binop_ = SHL)) {
     Return [$ishl_($sizenn(numtype), iN_1, iN_2)]
   }
   If (case(binop_) == SHR) {
     Let (SHR sx) = binop_
     Return [$ishr_($sizenn(numtype), sx, iN_1, iN_2)]
   }
   If ((binop_ = ROTL)) {
     Return [$irotl_($sizenn(numtype), iN_1, iN_2)]
   }
   If ((binop_ = ROTR)) {
     Return [$irotr_($sizenn(numtype), iN_1, iN_2)]
   }
 }
 Assert (type(numtype) == Fnn)
 If ((binop_ = ADD)) {
   Return $fadd_($sizenn(numtype), iN_1, iN_2)
 }
 If ((binop_ = SUB)) {
   Return $fsub_($sizenn(numtype), iN_1, iN_2)
 }
 If ((binop_ = MUL)) {
   Return $fmul_($sizenn(numtype), iN_1, iN_2)
 }
 If ((binop_ = DIV)) {
   Return $fdiv_($sizenn(numtype), iN_1, iN_2)
 }
 If ((binop_ = MIN)) {
   Return $fmin_($sizenn(numtype), iN_1, iN_2)
 }
 If ((binop_ = MAX)) {
   Return $fmax_($sizenn(numtype), iN_1, iN_2)
 }
 Assert ((binop_ = COPYSIGN))
 Return $fcopysign_($sizenn(numtype), iN_1, iN_2)
}
