Step_read/table.copy-trap-* x y {
 Assert (top_value(I32))
 Pop (I32.CONST n)
 Assert (top_value(I32))
 Pop (I32.CONST i)
 Assert (top_value(I32))
 Pop (I32.CONST j)
 If (((i + n) > |$table(z, y).REFS|)) {
   Trap
 }
 If (((j + n) > |$table(z, x).REFS|)) {
   Trap
 }
}

Step_read/table.init-trap-* x y {
 Assert (top_value(I32))
 Pop (I32.CONST n)
 Assert (top_value(I32))
 Pop (I32.CONST i)
 Assert (top_value(I32))
 Pop (I32.CONST j)
 If (((i + n) > |$elem(z, y).REFS|)) {
   Trap
 }
 If (((j + n) > |$table(z, x).REFS|)) {
   Trap
 }
}

Step_read/load-num-* nt ?() ao {
 Assert (top_value(I32))
 Pop (I32.CONST i)
 If ((((i + ao.OFFSET) + $nat$(($rat$($size(nt)) / $rat$(8)))) > |$mem(z, 0).BYTES|)) {
   Trap
 }
 Let c = $nbytes__1^-1(nt, $mem(z, 0).BYTES[(i + ao.OFFSET) : $nat$(($rat$($size(nt)) / $rat$(8)))])
 Push (nt.CONST c)
}

Step_read/load-pack-* Inn ?((n _ sx)) ao {
 Assert (top_value(I32))
 Pop (I32.CONST i)
 If ((((i + ao.OFFSET) + $nat$(($rat$(n) / $rat$(8)))) > |$mem(z, 0).BYTES|)) {
   Trap
 }
 Let c = $ibytes__1^-1(n, $mem(z, 0).BYTES[(i + ao.OFFSET) : $nat$(($rat$(n) / $rat$(8)))])
 Push (Inn.CONST $extend__(n, $size(Inn), sx, c))
}

Step_read/vload-shape-* V128 ?((SHAPE M X N _ sx)) ao {
 Assert (top_value(I32))
 Pop (I32.CONST i)
 If ((((i + ao.OFFSET) + $nat$(($rat$((M * N)) / $rat$(8)))) > |$mem(z, 0).BYTES|)) {
   Trap
 }
 Let j^N{j <- j*} = $ibytes__1^-1(M, $mem(z, 0).BYTES[((i + ao.OFFSET) + $nat$(($rat$((k * M)) / $rat$(8)))) : $nat$(($rat$(M) / $rat$(8)))])^(k<N){k <- _}
 Let Jnn = $jsize^-1((M * 2))
 Let c = $inv_lanes_((Jnn X N), $extend__(M, $jsize(Jnn), sx, j)^N{j <- j*})
 Push (V128.CONST c)
}

Step_read/vload-splat-* V128 ?((SPLAT N)) ao {
 Assert (top_value(I32))
 Pop (I32.CONST i)
 If ((((i + ao.OFFSET) + $nat$(($rat$(N) / $rat$(8)))) > |$mem(z, 0).BYTES|)) {
   Trap
 }
 Let $rat$(M) = ($rat$(128) / $rat$(N))
 Let Jnn = $jsize^-1(N)
 Let j = $ibytes__1^-1(N, $mem(z, 0).BYTES[(i + ao.OFFSET) : $nat$(($rat$(N) / $rat$(8)))])
 Let c = $inv_lanes_((Jnn X M), j^M{})
 Push (V128.CONST c)
}

Step_read/vload-zero-* V128 ?((ZERO N)) ao {
 Assert (top_value(I32))
 Pop (I32.CONST i)
 If ((((i + ao.OFFSET) + $nat$(($rat$(N) / $rat$(8)))) > |$mem(z, 0).BYTES|)) {
   Trap
 }
 Let j = $ibytes__1^-1(N, $mem(z, 0).BYTES[(i + ao.OFFSET) : $nat$(($rat$(N) / $rat$(8)))])
 Let c = $extend__(N, 128, U, j)
 Push (V128.CONST c)
}

Step_read/memory.copy-trap-* {
 Assert (top_value(I32))
 Pop (I32.CONST n)
 Assert (top_value(I32))
 Pop (I32.CONST i)
 Assert (top_value(I32))
 Pop (I32.CONST j)
 If (((i + n) > |$mem(z, 0).BYTES|)) {
   Trap
 }
 If (((j + n) > |$mem(z, 0).BYTES|)) {
   Trap
 }
}

Step_read/memory.init-trap-* x {
 Assert (top_value(I32))
 Pop (I32.CONST n)
 Assert (top_value(I32))
 Pop (I32.CONST i)
 Assert (top_value(I32))
 Pop (I32.CONST j)
 If (((i + n) > |$data(z, x).BYTES|)) {
   Trap
 }
 If (((j + n) > |$mem(z, 0).BYTES|)) {
   Trap
 }
}

Step/store-num-* nt ?() ao {
 Assert (top_value(nt))
 Pop (numtype_0.CONST c)
 Assert (top_value(I32))
 Pop (I32.CONST i)
 If ((((i + ao.OFFSET) + $nat$(($rat$($size(nt)) / $rat$(8)))) > |$mem(z, 0).BYTES|)) {
   Trap
 }
 Let b*{b <- b*} = $nbytes_(nt, c)
 $with_mem(z, 0, (i + ao.OFFSET), $nat$(($rat$($size(nt)) / $rat$(8))), b*{b <- b*})
}

Step/store-pack-* Inn ?(n) ao {
 Assert (top_value(Inn))
 Pop (numtype_0.CONST c)
 Assert (top_value(I32))
 Pop (I32.CONST i)
 If ((((i + ao.OFFSET) + $nat$(($rat$(n) / $rat$(8)))) > |$mem(z, 0).BYTES|)) {
   Trap
 }
 Let b*{b <- b*} = $ibytes_(n, $wrap__($size(Inn), n, c))
 $with_mem(z, 0, (i + ao.OFFSET), $nat$(($rat$(n) / $rat$(8))), b*{b <- b*})
}

Step_pure/unreachable {
 Trap
}

Step_pure/nop {
 Nop
}

Step_pure/drop {
 Assert (top_value())
 Pop val
}

Step_pure/select t*{t <- t*}?{t* <- t*?} {
 Assert (top_value(I32))
 Pop (I32.CONST c)
 Assert (top_value())
 Pop val_2
 Assert (top_value())
 Pop val_1
 If ((c =/= 0)) {
   Push val_1
 }
 Else {
   Push val_2
 }
}

Step_pure/if bt instr_1*{instr_1 <- instr_1*} instr_2*{instr_2 <- instr_2*} {
 Assert (top_value(I32))
 Pop (I32.CONST c)
 If ((c =/= 0)) {
   Execute (BLOCK bt instr_1*{instr_1 <- instr_1*})
 }
 Else {
   Execute (BLOCK bt instr_2*{instr_2 <- instr_2*})
 }
}

Step_pure/label {
 Pop_all val*{val <- val*}
 Assert (context_kind(LABEL_))
 Exit LABEL_
 Push val*{val <- val*}
}

Step_pure/br n' {
 Assert (context_kind(LABEL_))
 Let (LABEL_ n { instr'*{instr' <- instr*} }) = current_context(LABEL_)
 If ((n' = 0)) {
   Assert (top_values(n))
   Pop val^n{val <- val*}
   Pop_all val'*{val' <- val'*}
   Exit LABEL_
   Push val^n{val <- val*}
   Execute instr'*{instr' <- instr*}
 }
 Else {
   Pop_all val*{val <- val*}
   Let l = (n' - 1)
   Exit LABEL_
   Push val*{val <- val*}
   Execute (BR l)
 }
}

Step_pure/br_if l {
 Assert (top_value(I32))
 Pop (I32.CONST c)
 If ((c =/= 0)) {
   Execute (BR l)
 }
 Else {
   Nop
 }
}

Step_pure/br_table l*{l <- l*} l' {
 Assert (top_value(I32))
 Pop (I32.CONST i)
 If ((i < |l*{l <- l*}|)) {
   Execute (BR l*{l <- l*}[i])
 }
 Else {
   Execute (BR l')
 }
}

Step_pure/frame {
 Let (FRAME_ n { f }) = current_context(FRAME_)
 Assert (top_values(n))
 Assert (top_values(n))
 Pop val^n{val <- val*}
 Assert (context_kind(FRAME_))
 Exit FRAME_
 Push val^n{val <- val*}
}

Step_pure/return {
 If (context_kind(FRAME_)) {
   Let (FRAME_ n { f }) = current_context(FRAME_)
   Assert (top_values(n))
   Pop val^n{val <- val*}
   Pop_all val'*{val' <- val'*}
   Exit FRAME_
   Push val^n{val <- val*}
 }
 Else {
   Assert (context_kind(LABEL_))
   Pop_all val*{val <- val*}
   Exit LABEL_
   Push val*{val <- val*}
   Execute RETURN
 }
}

Step_pure/unop nt unop {
 Assert (top_value(nt))
 Pop (numtype_0.CONST c_1)
 If ((|$unop_(nt, unop, c_1)| <= 0)) {
   Trap
 }
 Let c = choose($unop_(nt, unop, c_1))
 Push (nt.CONST c)
}

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

Step_pure/testop nt testop {
 Assert (top_value(nt))
 Pop (numtype_0.CONST c_1)
 Let c = $testop_(nt, testop, c_1)
 Push (I32.CONST c)
}

Step_pure/relop nt relop {
 Assert (top_value(nt))
 Pop (numtype_0.CONST c_2)
 Assert (top_value(num))
 Pop (numtype_0.CONST c_1)
 Let c = $relop_(nt, relop, c_1, c_2)
 Push (I32.CONST c)
}

Step_pure/cvtop nt_2 nt_1 cvtop {
 Assert (top_value(nt_1))
 Pop (numtype_0.CONST c_1)
 If ((|$cvtop__(nt_1, nt_2, cvtop, c_1)| <= 0)) {
   Trap
 }
 Let c = choose($cvtop__(nt_1, nt_2, cvtop, c_1))
 Push (nt_2.CONST c)
}

Step_pure/ref.is_null {
 Assert (top_value(ref))
 Pop ref
 If (case(ref) == REF.NULL) {
   Push (I32.CONST 1)
 }
 Else {
   Push (I32.CONST 0)
 }
}

Step_pure/vvunop V128 vvunop {
 Assert (top_value(V128))
 Pop (V128.CONST c_1)
 Let c = $vvunop_(V128, vvunop, c_1)
 Push (V128.CONST c)
}

Step_pure/vvbinop V128 vvbinop {
 Assert (top_value(V128))
 Pop (V128.CONST c_2)
 Assert (top_value(V128))
 Pop (V128.CONST c_1)
 Let c = $vvbinop_(V128, vvbinop, c_1, c_2)
 Push (V128.CONST c)
}

Step_pure/vvternop V128 vvternop {
 Assert (top_value(V128))
 Pop (V128.CONST c_3)
 Assert (top_value(V128))
 Pop (V128.CONST c_2)
 Assert (top_value(V128))
 Pop (V128.CONST c_1)
 Let c = $vvternop_(V128, vvternop, c_1, c_2, c_3)
 Push (V128.CONST c)
}

Step_pure/vvtestop V128 ANY_TRUE {
 Assert (top_value(V128))
 Pop (V128.CONST c_1)
 Let c = $ine_($size(V128), c_1, 0)
 Push (I32.CONST c)
}

Step_pure/vunop sh vunop {
 Assert (top_value(V128))
 Pop (V128.CONST c_1)
 If ((|$vunop_(sh, vunop, c_1)| <= 0)) {
   Trap
 }
 Let c = choose($vunop_(sh, vunop, c_1))
 Push (V128.CONST c)
}

Step_pure/vbinop sh vbinop {
 Assert (top_value(V128))
 Pop (V128.CONST c_2)
 Assert (top_value(V128))
 Pop (V128.CONST c_1)
 If ((|$vbinop_(sh, vbinop, c_1, c_2)| <= 0)) {
   Trap
 }
 Let c = choose($vbinop_(sh, vbinop, c_1, c_2))
 Push (V128.CONST c)
}

Step_pure/vtestop (Jnn X N) ALL_TRUE {
 Assert (top_value(V128))
 Pop (V128.CONST c)
 Let ci_1*{ci_1 <- ci_1*} = $lanes_((Jnn X N), c)
 If ((ci_1 =/= 0)*{ci_1 <- ci_1*}) {
   Push (I32.CONST 1)
 }
 Else {
   Push (I32.CONST 0)
 }
}

Step_pure/vrelop sh vrelop {
 Assert (top_value(V128))
 Pop (V128.CONST c_2)
 Assert (top_value(V128))
 Pop (V128.CONST c_1)
 Let c = $vrelop_(sh, vrelop, c_1, c_2)
 Push (V128.CONST c)
}

Step_pure/vshiftop (Jnn X N) vshiftop {
 Assert (top_value(I32))
 Pop (I32.CONST n)
 Assert (top_value(V128))
 Pop (V128.CONST c_1)
 Let c'*{c' <- c'*} = $lanes_((Jnn X N), c_1)
 Let c = $inv_lanes_((Jnn X N), $vshiftop_((Jnn X N), vshiftop, c', n)*{c' <- c'*})
 Push (V128.CONST c)
}

Step_pure/vbitmask (Jnn X N) {
 Assert (top_value(V128))
 Pop (V128.CONST c)
 Let ci_1*{ci_1 <- ci_1*} = $lanes_((Jnn X N), c)
 Let ci = $ibits__1^-1(32, $ilt_($lsize(Jnn), S, ci_1, 0)*{ci_1 <- ci_1*} :: 0^$nat$(($int$(32) - $int$(N))){})
 Push (I32.CONST $irev_(32, ci))
}

Step_pure/vswizzle (Pnn X M) {
 Assert (top_value(V128))
 Pop (V128.CONST c_2)
 Assert (top_value(V128))
 Pop (V128.CONST c_1)
 Let c'*{c' <- c'*} = $lanes_((Pnn X M), c_1) :: 0^$nat$(($int$(256) - $int$(M))){}
 Let ci*{ci <- ci*} = $lanes_((Pnn X M), c_2)
 Assert ((ci*{ci <- ci*}[k] < |c'*{c' <- c'*}|)^(k<M){k <- _})
 Assert ((k < |ci*{ci <- ci*}|)^(k<M){k <- _})
 Let c = $inv_lanes_((Pnn X M), c'*{c' <- c'*}[ci*{ci <- ci*}[k]]^(k<M){})
 Push (V128.CONST c)
}

Step_pure/vshuffle (Pnn X N) i*{i <- i*} {
 Assert (top_value(V128))
 Pop (V128.CONST c_2)
 Assert (top_value(V128))
 Pop (V128.CONST c_1)
 Assert ((k < |i*{i <- i*}|)^(k<N){k <- _})
 Let c'*{c' <- c'*} = $lanes_((Pnn X N), c_1) :: $lanes_((Pnn X N), c_2)
 Assert ((i*{i <- i*}[k] < |c'*{c' <- c'*}|)^(k<N){k <- _})
 Let c = $inv_lanes_((Pnn X N), c'*{c' <- c'*}[i*{i <- i*}[k]]^(k<N){})
 Push (V128.CONST c)
}

Step_pure/vsplat (Lnn X N) {
 Assert (top_value())
 Pop (numtype_0.CONST c_1)
 Assert ((numtype_0 = $unpack(Lnn)))
 Let c = $inv_lanes_((Lnn X N), $packnum_(Lnn, c_1)^N{})
 Push (V128.CONST c)
}

Step_pure/vextract_lane (lanetype X N) sx'?{sx' <- sx'} i {
 Assert (top_value(V128))
 Pop (V128.CONST c_1)
 If (~(sx'?{sx' <- sx'} != None)) {
   Assert (type(lanetype) == numtype)
   Assert ((i < |$lanes_((lanetype X N), c_1)|))
   Let c_2 = $lanes_((lanetype X N), c_1)[i]
   Push (lanetype.CONST c_2)
 }
 Else {
   Assert (type(lanetype) == packtype)
   Let ?(sx) = sx'?{sx' <- sx'}
   Assert ((i < |$lanes_((lanetype X N), c_1)|))
   Let c_2 = $extend__($psize(lanetype), 32, sx, $lanes_((lanetype X N), c_1)[i])
   Push (I32.CONST c_2)
 }
}

Step_pure/vreplace_lane (Lnn X N) i {
 Assert (top_value())
 Pop (numtype_0.CONST c_2)
 Assert ((numtype_0 = $unpack(Lnn)))
 Assert (top_value(V128))
 Pop (V128.CONST c_1)
 Let c = $inv_lanes_((Lnn X N), update($lanes_((Lnn X N), c_1)[i], $packnum_(Lnn, c_2)))
 Push (V128.CONST c)
}

Step_pure/vextunop sh_1 sh_2 vextunop {
 Assert (top_value(V128))
 Pop (V128.CONST c_1)
 Let c = $vextunop__(sh_1, sh_2, vextunop, c_1)
 Push (V128.CONST c)
}

Step_pure/vextbinop sh_1 sh_2 vextbinop {
 Assert (top_value(V128))
 Pop (V128.CONST c_2)
 Assert (top_value(V128))
 Pop (V128.CONST c_1)
 Let c = $vextbinop__(sh_1, sh_2, vextbinop, c_1, c_2)
 Push (V128.CONST c)
}

Step_pure/vnarrow (Jnn_2 X N_2) (Jnn_1 X N_1) sx {
 Assert (top_value(V128))
 Pop (V128.CONST c_2)
 Assert (top_value(V128))
 Pop (V128.CONST c_1)
 Let ci_1*{ci_1 <- ci_1*} = $lanes_((Jnn_1 X N_1), c_1)
 Let ci_2*{ci_2 <- ci_2*} = $lanes_((Jnn_1 X N_1), c_2)
 Let cj_1*{cj_1 <- cj_1*} = $narrow__($lsize(Jnn_1), $lsize(Jnn_2), sx, ci_1)*{ci_1 <- ci_1*}
 Let cj_2*{cj_2 <- cj_2*} = $narrow__($lsize(Jnn_1), $lsize(Jnn_2), sx, ci_2)*{ci_2 <- ci_2*}
 Let c = $inv_lanes_((Jnn_2 X N_2), cj_1*{cj_1 <- cj_1*} :: cj_2*{cj_2 <- cj_2*})
 Push (V128.CONST c)
}

Step_pure/vcvtop (Lnn_2 X M) (Lnn_1 X M') vcvtop {
 Assert (top_value(V128))
 Pop (V128.CONST c_1)
 If ($halfop(vcvtop) != None) {
   Let ?(half) = $halfop(vcvtop)
   Let ci*{ci <- ci*} = $lanes_((Lnn_1 X M'), c_1)[$half(half, 0, M) : M]
   Let cj*{cj <- cj*}*{cj* <- cj**} = $setproduct_(lane_(Lnn_2), $vcvtop__((Lnn_1 X M'), (Lnn_2 X M), vcvtop, ci)*{ci <- ci*})
   If ((|$inv_lanes_((Lnn_2 X M), cj*{cj <- cj*})*{cj* <- cj**}| > 0)) {
     Let c = choose($inv_lanes_((Lnn_2 X M), cj*{cj <- cj*})*{cj* <- cj**})
     Push (V128.CONST c)
   }
 }
 Else if ((~($zeroop(vcvtop) != None) /\ (M = M'))) {
   Let ci*{ci <- ci*} = $lanes_((Lnn_1 X M'), c_1)
   Let cj*{cj <- cj*}*{cj* <- cj**} = $setproduct_(lane_(Lnn_2), $vcvtop__((Lnn_1 X M'), (Lnn_2 X M'), vcvtop, ci)*{ci <- ci*})
   If ((|$inv_lanes_((Lnn_2 X M'), cj*{cj <- cj*})*{cj* <- cj**}| > 0)) {
     Let c = choose($inv_lanes_((Lnn_2 X M'), cj*{cj <- cj*})*{cj* <- cj**})
     Push (V128.CONST c)
   }
 }
 If ((($zeroop(vcvtop) = ?(ZERO)) /\ (type(Lnn_1) == numtype /\ type(Lnn_2) == numtype))) {
   Let ci*{ci <- ci*} = $lanes_((Lnn_1 X M'), c_1)
   Let cj*{cj <- cj*}*{cj* <- cj**} = $setproduct_(lane_((nt_2 : numtype <: lanetype)), $vcvtop__((Lnn_1 X M'), (Lnn_2 X M), vcvtop, ci)*{ci <- ci*} :: [$zero(Lnn_2)]^M'{})
   If ((|$inv_lanes_((Lnn_2 X M), cj*{cj <- cj*})*{cj* <- cj**}| > 0)) {
     Let c = choose($inv_lanes_((Lnn_2 X M), cj*{cj <- cj*})*{cj* <- cj**})
     Push (V128.CONST c)
   }
 }
}

Step_pure/local.tee x {
 Assert (top_value())
 Pop val
 Push val
 Push val
 Execute (LOCAL.SET x)
}

Step_read/block bt instr*{instr <- instr*} {
 Let (t_1^k{t_1 <- t_1*} -> t_2^n{t_2 <- t_2*}) = $blocktype(z, bt)
 Assert (top_values(k))
 Pop val^k{val <- val*}
 Enter ((LABEL_ n { [] }), instr*{instr <- instr*} :: [LABEL_]) {
   Push val^k{val <- val*} 
 }
}

Step_read/loop bt instr*{instr <- instr*} {
 Let (t_1^k{t_1 <- t_1*} -> t_2^n{t_2 <- t_2*}) = $blocktype(z, bt)
 Assert (top_values(k))
 Pop val^k{val <- val*}
 Enter ((LABEL_ k { [(LOOP bt instr*{instr <- instr*})] }), instr*{instr <- instr*} :: [LABEL_]) {
   Push val^k{val <- val*} 
 }
}

Step_read/call x {
 Assert ((x < |$funcaddr(z)|))
 Execute (CALL_ADDR $funcaddr(z)[x])
}

Step_read/call_indirect x y {
 Assert (top_value(I32))
 Pop (I32.CONST i)
 If ((i >= |$table(z, x).REFS|)) {
   Trap
 }
 If (~(case($table(z, x).REFS[i]) == REF.FUNC_ADDR)) {
   Trap
 }
 Let (REF.FUNC_ADDR a) = $table(z, x).REFS[i]
 If ((a >= |$funcinst(z)|)) {
   Trap
 }
 If (($type(z, y) =/= $funcinst(z)[a].TYPE)) {
   Trap
 }
 Execute (CALL_ADDR a)
}

Step_read/call_addr a {
 Assert ((a < |$funcinst(z)|))
 Let { TYPE: (t_1^k{t_1 <- t_1*} -> t_2^n{t_2 <- t_2*}); MODULE: mm; CODE: func; } = $funcinst(z)[a]
 Let (FUNC x local_0*{local_0 <- local_0*} instr*{instr <- instr*}) = func
 Let (LOCAL t)*{t <- t*} = local_0*{local_0 <- local_0*}
 Assert (top_values(k))
 Pop val^k{val <- val*}
 Let f = { LOCALS: val^k{val <- val*} :: $default_(t)*{t <- t*}; MODULE: mm; }
 Enter ((FRAME_ n { f }), [FRAME_]) {
   Enter ((LABEL_ n { [] }), instr*{instr <- instr*} :: [LABEL_]) { 
   } 
 }
}

Step_read/ref.func x {
 Assert ((x < |$funcaddr(z)|))
 Push (REF.FUNC_ADDR $funcaddr(z)[x])
}

Step_read/local.get x {
 Push $local(z, x)
}

Step_read/global.get x {
 Push $global(z, x).VALUE
}

Step_read/table.get x {
 Assert (top_value(I32))
 Pop (I32.CONST i)
 If ((i >= |$table(z, x).REFS|)) {
   Trap
 }
 Push $table(z, x).REFS[i]
}

Step_read/table.size x {
 Let n = |$table(z, x).REFS|
 Push (I32.CONST n)
}

Step_read/table.fill x {
 Assert (top_value(I32))
 Pop (I32.CONST n)
 Assert (top_value())
 Pop val
 Assert (top_value(I32))
 Pop (I32.CONST i)
 If (((i + n) > |$table(z, x).REFS|)) {
   Trap
 }
 If ((n = 0)) {
   Nop
 }
 Else {
   Push (I32.CONST i)
   Push val
   Execute (TABLE.SET x)
   Push (I32.CONST (i + 1))
   Push val
   Push (I32.CONST $nat$(($int$(n) - $int$(1))))
   Execute (TABLE.FILL x)
 }
}

Step_read/table.copy x y {
 Assert (top_value(I32))
 Pop (I32.CONST n)
 Assert (top_value(I32))
 Pop (I32.CONST i)
 Assert (top_value(I32))
 Pop (I32.CONST j)
 If (((i + n) > |$table(z, y).REFS|)) {
   Trap
 }
 If (((j + n) > |$table(z, x).REFS|)) {
   Trap
 }
 If ((n = 0)) {
   Nop
 }
 Else {
   If ((j <= i)) {
     Push (I32.CONST j)
     Push (I32.CONST i)
     Execute (TABLE.GET y)
     Execute (TABLE.SET x)
     Push (I32.CONST (j + 1))
     Push (I32.CONST (i + 1))
   }
   Else {
     Push (I32.CONST $nat$(($int$((j + n)) - $int$(1))))
     Push (I32.CONST $nat$(($int$((i + n)) - $int$(1))))
     Execute (TABLE.GET y)
     Execute (TABLE.SET x)
     Push (I32.CONST j)
     Push (I32.CONST i)
   }
   Push (I32.CONST $nat$(($int$(n) - $int$(1))))
   Execute (TABLE.COPY x y)
 }
}

Step_read/table.init x y {
 Assert (top_value(I32))
 Pop (I32.CONST n)
 Assert (top_value(I32))
 Pop (I32.CONST i)
 Assert (top_value(I32))
 Pop (I32.CONST j)
 If (((i + n) > |$elem(z, y).REFS|)) {
   Trap
 }
 If (((j + n) > |$table(z, x).REFS|)) {
   Trap
 }
 If ((n = 0)) {
   Nop
 }
 Else {
   Assert ((i < |$elem(z, y).REFS|))
   Push (I32.CONST j)
   Push $elem(z, y).REFS[i]
   Execute (TABLE.SET x)
   Push (I32.CONST (j + 1))
   Push (I32.CONST (i + 1))
   Push (I32.CONST $nat$(($int$(n) - $int$(1))))
   Execute (TABLE.INIT x y)
 }
}

Step_read/load nt loadop_?{loadop_ <- loadop_} ao {
 Assert (top_value(I32))
 Pop (I32.CONST i)
 If (~(loadop_?{loadop_ <- loadop_} != None)) {
   If ((((i + ao.OFFSET) + $nat$(($rat$($size(nt)) / $rat$(8)))) > |$mem(z, 0).BYTES|)) {
     Trap
   }
   Let c = $nbytes__1^-1(nt, $mem(z, 0).BYTES[(i + ao.OFFSET) : $nat$(($rat$($size(nt)) / $rat$(8)))])
   Push (nt.CONST c)
 }
 Else {
   Assert (type(nt) == Inn)
   Let ?(loadop_0) = loadop_?{loadop_ <- loadop_}
   Let (n _ sx) = loadop_0
   If ((((i + ao.OFFSET) + $nat$(($rat$(n) / $rat$(8)))) > |$mem(z, 0).BYTES|)) {
     Trap
   }
   Let c = $ibytes__1^-1(n, $mem(z, 0).BYTES[(i + ao.OFFSET) : $nat$(($rat$(n) / $rat$(8)))])
   Push (nt.CONST $extend__(n, $size(nt), sx, c))
 }
}

Step_read/vload V128 vloadop?{vloadop <- vloadop} ao {
 Assert (top_value(I32))
 Pop (I32.CONST i)
 If (~(vloadop?{vloadop <- vloadop} != None)) {
   If ((((i + ao.OFFSET) + $nat$(($rat$($size(V128)) / $rat$(8)))) > |$mem(z, 0).BYTES|)) {
     Trap
   }
   Let c = $vbytes__1^-1(V128, $mem(z, 0).BYTES[(i + ao.OFFSET) : $nat$(($rat$($size(V128)) / $rat$(8)))])
   Push (V128.CONST c)
 }
 Else {
   Let ?(vloadop_0) = vloadop?{vloadop <- vloadop}
   If (case(vloadop_0) == SHAPE) {
     Let (SHAPE M X N _ sx) = vloadop_0
     If ((((i + ao.OFFSET) + $nat$(($rat$((M * N)) / $rat$(8)))) > |$mem(z, 0).BYTES|)) {
       Trap
     }
     Let j^N{j <- j*} = $ibytes__1^-1(M, $mem(z, 0).BYTES[((i + ao.OFFSET) + $nat$(($rat$((k * M)) / $rat$(8)))) : $nat$(($rat$(M) / $rat$(8)))])^(k<N){k <- _}
     Let Jnn = $jsize^-1((M * 2))
     Let c = $inv_lanes_((Jnn X N), $extend__(M, $jsize(Jnn), sx, j)^N{j <- j*})
     Push (V128.CONST c)
   }
   If (case(vloadop_0) == SPLAT) {
     Let (SPLAT N) = vloadop_0
     If ((((i + ao.OFFSET) + $nat$(($rat$(N) / $rat$(8)))) > |$mem(z, 0).BYTES|)) {
       Trap
     }
     Let $rat$(M) = ($rat$(128) / $rat$(N))
     Let Jnn = $jsize^-1(N)
     Let j = $ibytes__1^-1(N, $mem(z, 0).BYTES[(i + ao.OFFSET) : $nat$(($rat$(N) / $rat$(8)))])
     Let c = $inv_lanes_((Jnn X M), j^M{})
     Push (V128.CONST c)
   }
   If (case(vloadop_0) == ZERO) {
     Let (ZERO N) = vloadop_0
     If ((((i + ao.OFFSET) + $nat$(($rat$(N) / $rat$(8)))) > |$mem(z, 0).BYTES|)) {
       Trap
     }
     Let j = $ibytes__1^-1(N, $mem(z, 0).BYTES[(i + ao.OFFSET) : $nat$(($rat$(N) / $rat$(8)))])
     Let c = $extend__(N, 128, U, j)
     Push (V128.CONST c)
   }
 }
}

Step_read/vload_lane V128 N ao j {
 Assert (top_value(V128))
 Pop (V128.CONST c_1)
 Assert (top_value(I32))
 Pop (I32.CONST i)
 If ((((i + ao.OFFSET) + $nat$(($rat$(N) / $rat$(8)))) > |$mem(z, 0).BYTES|)) {
   Trap
 }
 Let $rat$(M) = ($rat$(128) / $rat$(N))
 Let Jnn = $jsize^-1(N)
 Let k = $ibytes__1^-1(N, $mem(z, 0).BYTES[(i + ao.OFFSET) : $nat$(($rat$(N) / $rat$(8)))])
 Let c = $inv_lanes_((Jnn X M), update($lanes_((Jnn X M), c_1)[j], k))
 Push (V128.CONST c)
}

Step_read/memory.size {
 Let ((n * 64) * $Ki()) = |$mem(z, 0).BYTES|
 Push (I32.CONST n)
}

Step_read/memory.fill {
 Assert (top_value(I32))
 Pop (I32.CONST n)
 Assert (top_value())
 Pop val
 Assert (top_value(I32))
 Pop (I32.CONST i)
 If (((i + n) > |$mem(z, 0).BYTES|)) {
   Trap
 }
 If ((n = 0)) {
   Nop
 }
 Else {
   Push (I32.CONST i)
   Push val
   Execute (STORE I32 ?(8) $memarg0())
   Push (I32.CONST (i + 1))
   Push val
   Push (I32.CONST $nat$(($int$(n) - $int$(1))))
   Execute MEMORY.FILL
 }
}

Step_read/memory.copy {
 Assert (top_value(I32))
 Pop (I32.CONST n)
 Assert (top_value(I32))
 Pop (I32.CONST i)
 Assert (top_value(I32))
 Pop (I32.CONST j)
 If (((i + n) > |$mem(z, 0).BYTES|)) {
   Trap
 }
 If (((j + n) > |$mem(z, 0).BYTES|)) {
   Trap
 }
 If ((n = 0)) {
   Nop
 }
 Else {
   If ((j <= i)) {
     Push (I32.CONST j)
     Push (I32.CONST i)
     Execute (LOAD I32 ?((8 _ U)) $memarg0())
     Execute (STORE I32 ?(8) $memarg0())
     Push (I32.CONST (j + 1))
     Push (I32.CONST (i + 1))
   }
   Else {
     Push (I32.CONST $nat$(($int$((j + n)) - $int$(1))))
     Push (I32.CONST $nat$(($int$((i + n)) - $int$(1))))
     Execute (LOAD I32 ?((8 _ U)) $memarg0())
     Execute (STORE I32 ?(8) $memarg0())
     Push (I32.CONST j)
     Push (I32.CONST i)
   }
   Push (I32.CONST $nat$(($int$(n) - $int$(1))))
   Execute MEMORY.COPY
 }
}

Step_read/memory.init x {
 Assert (top_value(I32))
 Pop (I32.CONST n)
 Assert (top_value(I32))
 Pop (I32.CONST i)
 Assert (top_value(I32))
 Pop (I32.CONST j)
 If (((i + n) > |$data(z, x).BYTES|)) {
   Trap
 }
 If (((j + n) > |$mem(z, 0).BYTES|)) {
   Trap
 }
 If ((n = 0)) {
   Nop
 }
 Else {
   Assert ((i < |$data(z, x).BYTES|))
   Push (I32.CONST j)
   Push (I32.CONST $data(z, x).BYTES[i])
   Execute (STORE I32 ?(8) $memarg0())
   Push (I32.CONST (j + 1))
   Push (I32.CONST (i + 1))
   Push (I32.CONST $nat$(($int$(n) - $int$(1))))
   Execute (MEMORY.INIT x)
 }
}

Step/local.set x {
 Assert (top_value())
 Pop val
 $with_local(z, x, val)
}

Step/global.set x {
 Assert (top_value())
 Pop val
 $with_global(z, x, val)
}

Step/table.set x {
 Assert (top_value(ref))
 Pop ref
 Assert (top_value(I32))
 Pop (I32.CONST i)
 If ((i >= |$table(z, x).REFS|)) {
   Trap
 }
 $with_table(z, x, i, ref)
}

Step/table.grow x {
 Assert (top_value(I32))
 Pop (I32.CONST n)
 Assert (top_value(ref))
 Pop ref
 Either {
   Let ti = $growtable($table(z, x), n, ref)
   Push (I32.CONST |$table(z, x).REFS|)
   $with_tableinst(z, x, ti)
 }
 Or {
   Push (I32.CONST $inv_signed_(32, -($int$(1))))
 }
}

Step/elem.drop x {
 $with_elem(z, x, [])
}

Step/store nt sz?{sz <- sz} ao {
 Assert (top_value(num))
 Pop (nt'.CONST c)
 Assert (top_value())
 Pop (I32.CONST i)
 Assert ((nt = nt'))
 If (~(sz?{sz <- sz} != None)) {
   If ((((i + ao.OFFSET) + $nat$(($rat$($size(nt')) / $rat$(8)))) > |$mem(z, 0).BYTES|)) {
     Trap
   }
   Let b*{b <- b*} = $nbytes_(nt', c)
   $with_mem(z, 0, (i + ao.OFFSET), $nat$(($rat$($size(nt')) / $rat$(8))), b*{b <- b*})
 }
 Else {
   Assert (type(nt') == Inn)
   Let ?(n) = sz?{sz <- sz}
   If ((((i + ao.OFFSET) + $nat$(($rat$(n) / $rat$(8)))) > |$mem(z, 0).BYTES|)) {
     Trap
   }
   Let b*{b <- b*} = $ibytes_(n, $wrap__($size(nt'), n, c))
   $with_mem(z, 0, (i + ao.OFFSET), $nat$(($rat$(n) / $rat$(8))), b*{b <- b*})
 }
}

Step/vstore V128 ao {
 Assert (top_value(V128))
 Pop (V128.CONST c)
 Assert (top_value(I32))
 Pop (I32.CONST i)
 If ((((i + ao.OFFSET) + $nat$(($rat$($size(V128)) / $rat$(8)))) > |$mem(z, 0).BYTES|)) {
   Trap
 }
 Let b*{b <- b*} = $vbytes_(V128, c)
 $with_mem(z, 0, (i + ao.OFFSET), $nat$(($rat$($size(V128)) / $rat$(8))), b*{b <- b*})
}

Step/vstore_lane V128 N ao j {
 Assert (top_value(V128))
 Pop (V128.CONST c)
 Assert (top_value(I32))
 Pop (I32.CONST i)
 If ((((i + ao.OFFSET) + N) > |$mem(z, 0).BYTES|)) {
   Trap
 }
 Let $rat$(M) = ($rat$(128) / $rat$(N))
 Let Jnn = $jsize^-1(N)
 Assert ((j < |$lanes_((Jnn X M), c)|))
 Let b*{b <- b*} = $ibytes_(N, $lanes_((Jnn X M), c)[j])
 $with_mem(z, 0, (i + ao.OFFSET), $nat$(($rat$(N) / $rat$(8))), b*{b <- b*})
}

Step/memory.grow {
 Assert (top_value(I32))
 Pop (I32.CONST n)
 Either {
   Let mi = $growmemory($mem(z, 0), n)
   Push (I32.CONST $nat$(($rat$(|$mem(z, 0).BYTES|) / $rat$((64 * $Ki())))))
   $with_meminst(z, 0, mi)
 }
 Or {
   Push (I32.CONST $inv_signed_(32, -($int$(1))))
 }
}

Step/data.drop x {
 $with_data(z, x, [])
}

Ki {
 Return 1024
}

min i j {
 If ((i <= j)) {
   Return i
 }
 Return j
}

sum n''*{n'' <- n''} {
 If ((n''*{n'' <- n''} = [])) {
   Return 0
 }
 Let [n] :: n'*{n' <- n'*} = n''*{n'' <- n''}
 Return (n + $sum(n'*{n' <- n'*}))
}

opt_ X X*{X <- X} {
 If ((X*{X <- X} = [])) {
   Return ?()
 }
 If ((|X*{X <- X}| = 1)) {
   Let [w] = X*{X <- X}
   Return ?(w)
 }
 Fail
}

list_ X X?{X <- X} {
 If (~(X?{X <- X} != None)) {
   Return []
 }
 Let ?(w) = X?{X <- X}
 Return [w]
}

concat_ X X*{X <- X} {
 If ((X*{X <- X} = [])) {
   Return []
 }
 Let [w*{w <- w*}] :: w'*{w' <- w'*}*{w'* <- w'**} = X*{X <- X}
 Return w*{w <- w*} :: $concat_(X, w'*{w' <- w'*}*{w'* <- w'**})
}

setproduct2_ X w_1 X*{X <- X} {
 If ((X*{X <- X} = [])) {
   Return []
 }
 Let [w'*{w' <- w'*}] :: w*{w <- w*}*{w* <- w**} = X*{X <- X}
 Return [[w_1] :: w'*{w' <- w'*}] :: $setproduct2_(X, w_1, w*{w <- w*}*{w* <- w**})
}

setproduct1_ X X*{X <- X} w*{w <- w*}*{w* <- w**} {
 If ((X*{X <- X} = [])) {
   Return []
 }
 Let [w_1] :: w'*{w' <- w'*} = X*{X <- X}
 Return $setproduct2_(X, w_1, w*{w <- w*}*{w* <- w**}) :: $setproduct1_(X, w'*{w' <- w'*}, w*{w <- w*}*{w* <- w**})
}

setproduct_ X X*{X <- X} {
 If ((X*{X <- X} = [])) {
   Return [[]]
 }
 Let [w_1*{w_1 <- w_1*}] :: w*{w <- w*}*{w* <- w**} = X*{X <- X}
 Return $setproduct1_(X, w_1*{w_1 <- w_1*}, $setproduct_(X, w*{w <- w*}*{w* <- w**}))
}

disjoint_ X X*{X <- X} {
 If ((X*{X <- X} = [])) {
   Return true
 }
 Let [w] :: w'*{w' <- w'*} = X*{X <- X}
 Return (~(w is contained in w'*{w' <- w'*}) /\ $disjoint_(X, w'*{w' <- w'*}))
}

signif N {
 If ((N = 32)) {
   Return 23
 }
 If ((N = 64)) {
   Return 52
 }
 Fail
}

expon N {
 If ((N = 32)) {
   Return 8
 }
 If ((N = 64)) {
   Return 11
 }
 Fail
}

M N {
 Return $signif(N)
}

E N {
 Return $expon(N)
}

fzero N {
 Return (POS (SUBNORM 0))
}

fone N {
 Return (POS (NORM 1 $int$(0)))
}

canon_ N {
 Return (2 ^ $nat$(($int$($signif(N)) - $int$(1))))
}

lanetype (Lnn X N) {
 Return Lnn
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

psize packtype {
 If ((packtype = I8)) {
   Return 8
 }
 Assert ((packtype = I16))
 Return 16
}

lsize lanetype {
 If (type(lanetype) == numtype) {
   Return $size(lanetype)
 }
 Assert (type(lanetype) == packtype)
 Return $psize(lanetype)
}

isize Inn {
 Return $size(Inn)
}

jsize Jnn {
 Return $lsize(Jnn)
}

fsize Fnn {
 Return $size(Fnn)
}

sizenn nt {
 Return $size(nt)
}

sizenn1 nt {
 Return $size(nt)
}

sizenn2 nt {
 Return $size(nt)
}

lsizenn lt {
 Return $lsize(lt)
}

lsizenn1 lt {
 Return $lsize(lt)
}

lsizenn2 lt {
 Return $lsize(lt)
}

inv_isize n {
 If ((n = 32)) {
   Return I32
 }
 If ((n = 64)) {
   Return I64
 }
 Fail
}

inv_jsize n {
 If ((n = 8)) {
   Return I8
 }
 If ((n = 16)) {
   Return I16
 }
 If ((n = 32)) {
   Return I32
 }
 If ((n = 64)) {
   Return I64
 }
 Fail
}

inv_fsize n {
 If ((n = 32)) {
   Return F32
 }
 If ((n = 64)) {
   Return F64
 }
 Fail
}

zero numtype {
 If (type(numtype) == Inn) {
   Return 0
 }
 Assert (type(numtype) == Fnn)
 Return $fzero($size(numtype))
}

dim (Lnn X N) {
 Return N
}

shsize (Lnn X N) {
 Return ($lsize(Lnn) * N)
}

concat_bytes byte*{byte <- byte} {
 If ((byte*{byte <- byte} = [])) {
   Return []
 }
 Let [b*{b <- b*}] :: b'*{b' <- b'*}*{b'* <- b'**} = byte*{byte <- byte}
 Return b*{b <- b*} :: $concat_bytes(b'*{b' <- b'*}*{b'* <- b'**})
}

unpack lanetype {
 If (type(lanetype) == numtype) {
   Return lanetype
 }
 Assert (type(lanetype) == packtype)
 Return I32
}

shunpack (Lnn X N) {
 Return $unpack(Lnn)
}

funcsxt externtype'*{externtype' <- externtype'} {
 If ((externtype'*{externtype' <- externtype'} = [])) {
   Return []
 }
 Let [externtype_0] :: xt*{xt <- xt*} = externtype'*{externtype' <- externtype'}
 If (case(externtype_0) == FUNC) {
   Let (FUNC ft) = externtype_0
   Return [ft] :: $funcsxt(xt*{xt <- xt*})
 }
 Let [externtype] :: xt*{xt <- xt*} = externtype'*{externtype' <- externtype'}
 Return $funcsxt(xt*{xt <- xt*})
}

globalsxt externtype'*{externtype' <- externtype'} {
 If ((externtype'*{externtype' <- externtype'} = [])) {
   Return []
 }
 Let [externtype_0] :: xt*{xt <- xt*} = externtype'*{externtype' <- externtype'}
 If (case(externtype_0) == GLOBAL) {
   Let (GLOBAL gt) = externtype_0
   Return [gt] :: $globalsxt(xt*{xt <- xt*})
 }
 Let [externtype] :: xt*{xt <- xt*} = externtype'*{externtype' <- externtype'}
 Return $globalsxt(xt*{xt <- xt*})
}

tablesxt externtype'*{externtype' <- externtype'} {
 If ((externtype'*{externtype' <- externtype'} = [])) {
   Return []
 }
 Let [externtype_0] :: xt*{xt <- xt*} = externtype'*{externtype' <- externtype'}
 If (case(externtype_0) == TABLE) {
   Let (TABLE tt) = externtype_0
   Return [tt] :: $tablesxt(xt*{xt <- xt*})
 }
 Let [externtype] :: xt*{xt <- xt*} = externtype'*{externtype' <- externtype'}
 Return $tablesxt(xt*{xt <- xt*})
}

memsxt externtype'*{externtype' <- externtype'} {
 If ((externtype'*{externtype' <- externtype'} = [])) {
   Return []
 }
 Let [externtype_0] :: xt*{xt <- xt*} = externtype'*{externtype' <- externtype'}
 If (case(externtype_0) == MEM) {
   Let (MEM mt) = externtype_0
   Return [mt] :: $memsxt(xt*{xt <- xt*})
 }
 Let [externtype] :: xt*{xt <- xt*} = externtype'*{externtype' <- externtype'}
 Return $memsxt(xt*{xt <- xt*})
}

dataidx_instr instr {
 If (case(instr) == MEMORY.INIT) {
   Let (MEMORY.INIT x) = instr
   Return [x]
 }
 If (case(instr) == DATA.DROP) {
   Let (DATA.DROP x) = instr
   Return [x]
 }
 Return []
}

dataidx_instrs instr''*{instr'' <- instr''} {
 If ((instr''*{instr'' <- instr''} = [])) {
   Return []
 }
 Let [instr] :: instr'*{instr' <- instr'*} = instr''*{instr'' <- instr''}
 Return $dataidx_instr(instr) :: $dataidx_instrs(instr'*{instr' <- instr'*})
}

dataidx_expr in*{in <- in*} {
 Return $dataidx_instrs(in*{in <- in*})
}

dataidx_func (FUNC x loc*{loc <- loc*} e) {
 Return $dataidx_expr(e)
}

dataidx_funcs func''*{func'' <- func''} {
 If ((func''*{func'' <- func''} = [])) {
   Return []
 }
 Let [func] :: func'*{func' <- func'*} = func''*{func'' <- func''}
 Return $dataidx_func(func) :: $dataidx_funcs(func'*{func' <- func'*})
}

memarg0 {
 Return { ALIGN: 0; OFFSET: 0; }
}

bool b {
 If ((b = false)) {
   Return 0
 }
 Assert ((b = true))
 Return 1
}

signed_ N i {
 If ((i < (2 ^ $nat$(($int$(N) - $int$(1)))))) {
   Return $int$(i)
 }
 Assert (((2 ^ $nat$(($int$(N) - $int$(1)))) <= i))
 Assert ((i < (2 ^ N)))
 Return ($int$(i) - $int$((2 ^ N)))
}

inv_signed_ N i {
 If ((($int$(0) <= i) /\ (i < $int$((2 ^ $nat$(($int$(N) - $int$(1)))))))) {
   Return $nat$(i)
 }
 Assert ((-($int$((2 ^ $nat$(($int$(N) - $int$(1)))))) <= i))
 Assert ((i < $int$(0)))
 Return $nat$((i + $int$((2 ^ N))))
}

sat_u_ N i {
 If ((i < $int$(0))) {
   Return 0
 }
 If ((i > ($int$((2 ^ N)) - $int$(1)))) {
   Return $nat$(($int$((2 ^ N)) - $int$(1)))
 }
 Return $nat$(i)
}

sat_s_ N i {
 If ((i < -($int$((2 ^ $nat$(($int$(N) - $int$(1)))))))) {
   Return -($int$((2 ^ $nat$(($int$(N) - $int$(1))))))
 }
 If ((i > ($int$((2 ^ $nat$(($int$(N) - $int$(1))))) - $int$(1)))) {
   Return ($int$((2 ^ $nat$(($int$(N) - $int$(1))))) - $int$(1))
 }
 Return i
}

unop_ numtype unop_ iN {
 If (type(numtype) == Inn) {
   If ((unop_ = CLZ)) {
     Return [$iclz_($sizenn(numtype), iN)]
   }
   If ((unop_ = CTZ)) {
     Return [$ictz_($sizenn(numtype), iN)]
   }
   If ((unop_ = POPCNT)) {
     Return [$ipopcnt_($sizenn(numtype), iN)]
   }
   If (case(unop_) == EXTEND) {
     Let (EXTEND M) = unop_
     Return [$extend__(M, $sizenn(numtype), S, $wrap__($sizenn(numtype), M, iN))]
   }
 }
 Assert (type(numtype) == Fnn)
 If ((unop_ = ABS)) {
   Return $fabs_($sizenn(numtype), iN)
 }
 If ((unop_ = NEG)) {
   Return $fneg_($sizenn(numtype), iN)
 }
 If ((unop_ = SQRT)) {
   Return $fsqrt_($sizenn(numtype), iN)
 }
 If ((unop_ = CEIL)) {
   Return $fceil_($sizenn(numtype), iN)
 }
 If ((unop_ = FLOOR)) {
   Return $ffloor_($sizenn(numtype), iN)
 }
 If ((unop_ = TRUNC)) {
   Return $ftrunc_($sizenn(numtype), iN)
 }
 Assert ((unop_ = NEAREST))
 Return $fnearest_($sizenn(numtype), iN)
}

iadd_ N i_1 i_2 {
 Return ((i_1 + i_2) \ (2 ^ N))
}

idiv_ N sx i_1 i_2 {
 If ((sx = U)) {
   If ((i_2 = 0)) {
     Return ?()
   }
   Return ?($nat$($truncz(($rat$(i_1) / $rat$(i_2)))))
 }
 Assert ((sx = S))
 If ((i_2 = 0)) {
   Return ?()
 }
 If ((($rat$($signed_(N, i_1)) / $rat$($signed_(N, i_2))) = $rat$((2 ^ $nat$(($int$(N) - $int$(1))))))) {
   Return ?()
 }
 Return ?($inv_signed_(N, $truncz(($rat$($signed_(N, i_1)) / $rat$($signed_(N, i_2))))))
}

imul_ N i_1 i_2 {
 Return ((i_1 * i_2) \ (2 ^ N))
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

isub_ N i_1 i_2 {
 Return $nat$((($int$(((2 ^ N) + i_1)) - $int$(i_2)) \ $int$((2 ^ N))))
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

ieqz_ N i_1 {
 Return $bool((i_1 = 0))
}

testop_ Inn EQZ iN {
 Return $ieqz_($sizenn(Inn), iN)
}

ieq_ N i_1 i_2 {
 Return $bool((i_1 = i_2))
}

ige_ N sx i_1 i_2 {
 If ((sx = U)) {
   Return $bool((i_1 >= i_2))
 }
 Assert ((sx = S))
 Return $bool(($signed_(N, i_1) >= $signed_(N, i_2)))
}

igt_ N sx i_1 i_2 {
 If ((sx = U)) {
   Return $bool((i_1 > i_2))
 }
 Assert ((sx = S))
 Return $bool(($signed_(N, i_1) > $signed_(N, i_2)))
}

ile_ N sx i_1 i_2 {
 If ((sx = U)) {
   Return $bool((i_1 <= i_2))
 }
 Assert ((sx = S))
 Return $bool(($signed_(N, i_1) <= $signed_(N, i_2)))
}

ilt_ N sx i_1 i_2 {
 If ((sx = U)) {
   Return $bool((i_1 < i_2))
 }
 Assert ((sx = S))
 Return $bool(($signed_(N, i_1) < $signed_(N, i_2)))
}

ine_ N i_1 i_2 {
 Return $bool((i_1 =/= i_2))
}

relop_ numtype relop_ iN_1 iN_2 {
 If (type(numtype) == Inn) {
   If ((relop_ = EQ)) {
     Return $ieq_($sizenn(numtype), iN_1, iN_2)
   }
   If ((relop_ = NE)) {
     Return $ine_($sizenn(numtype), iN_1, iN_2)
   }
   If (case(relop_) == LT) {
     Let (LT sx) = relop_
     Return $ilt_($sizenn(numtype), sx, iN_1, iN_2)
   }
   If (case(relop_) == GT) {
     Let (GT sx) = relop_
     Return $igt_($sizenn(numtype), sx, iN_1, iN_2)
   }
   If (case(relop_) == LE) {
     Let (LE sx) = relop_
     Return $ile_($sizenn(numtype), sx, iN_1, iN_2)
   }
   If (case(relop_) == GE) {
     Let (GE sx) = relop_
     Return $ige_($sizenn(numtype), sx, iN_1, iN_2)
   }
 }
 Assert (type(numtype) == Fnn)
 If ((relop_ = EQ)) {
   Return $feq_($sizenn(numtype), iN_1, iN_2)
 }
 If ((relop_ = NE)) {
   Return $fne_($sizenn(numtype), iN_1, iN_2)
 }
 If ((relop_ = LT)) {
   Return $flt_($sizenn(numtype), iN_1, iN_2)
 }
 If ((relop_ = GT)) {
   Return $fgt_($sizenn(numtype), iN_1, iN_2)
 }
 If ((relop_ = LE)) {
   Return $fle_($sizenn(numtype), iN_1, iN_2)
 }
 Assert ((relop_ = GE))
 Return $fge_($sizenn(numtype), iN_1, iN_2)
}

cvtop__ numtype numtype' cvtop iN_1 {
 If ((type(numtype) == Inn /\ type(numtype') == Inn)) {
   If (case(cvtop) == EXTEND) {
     Let (EXTEND sx) = cvtop
     Return [$extend__($sizenn1(numtype), $sizenn2(numtype'), sx, iN_1)]
   }
   If ((cvtop = WRAP)) {
     Return [$wrap__($sizenn1(numtype), $sizenn2(numtype'), iN_1)]
   }
 }
 If ((type(numtype) == Fnn /\ type(numtype') == Inn)) {
   If (case(cvtop) == TRUNC) {
     Let (TRUNC sx) = cvtop
     Return $list_(num_((Inn_2 : Inn <: numtype)), $trunc__($sizenn1(numtype), $sizenn2(numtype'), sx, iN_1))
   }
   If (case(cvtop) == TRUNC_SAT) {
     Let (TRUNC_SAT sx) = cvtop
     Return $list_(num_((Inn_2 : Inn <: numtype)), $trunc_sat__($sizenn1(numtype), $sizenn2(numtype'), sx, iN_1))
   }
 }
 If ((type(numtype) == Inn /\ (type(numtype') == Fnn /\ case(cvtop) == CONVERT))) {
   Let (CONVERT sx) = cvtop
   Return [$convert__($sizenn1(numtype), $sizenn2(numtype'), sx, iN_1)]
 }
 If ((type(numtype) == Fnn /\ type(numtype') == Fnn)) {
   If ((cvtop = PROMOTE)) {
     Return $promote__($sizenn1(numtype), $sizenn2(numtype'), iN_1)
   }
   If ((cvtop = DEMOTE)) {
     Return $demote__($sizenn1(numtype), $sizenn2(numtype'), iN_1)
   }
 }
 If ((type(numtype) == Inn /\ (type(numtype') == Fnn /\ ((cvtop = REINTERPRET) /\ ($size(numtype) = $size(numtype')))))) {
   Return [$reinterpret__(numtype, numtype', iN_1)]
 }
 Assert (type(numtype) == Fnn)
 Assert (type(numtype') == Inn)
 Assert ((cvtop = REINTERPRET))
 Assert (($size(numtype) = $size(numtype')))
 Return [$reinterpret__(numtype, numtype', iN_1)]
}

inez_ N i_1 {
 Return $bool((i_1 =/= 0))
}

ineg_ N i_1 {
 Return $nat$((($int$((2 ^ N)) - $int$(i_1)) \ $int$((2 ^ N))))
}

iabs_ N i_1 {
 If (($signed_(N, i_1) >= $int$(0))) {
   Return i_1
 }
 Return $ineg_(N, i_1)
}

imin_ N sx i_1 i_2 {
 If ((sx = U)) {
   If ((i_1 <= i_2)) {
     Return i_1
   }
   Return i_2
 }
 Assert ((sx = S))
 If (($signed_(N, i_1) <= $signed_(N, i_2))) {
   Return i_1
 }
 Return i_2
}

imax_ N sx i_1 i_2 {
 If ((sx = U)) {
   If ((i_1 >= i_2)) {
     Return i_1
   }
   Return i_2
 }
 Assert ((sx = S))
 If (($signed_(N, i_1) >= $signed_(N, i_2))) {
   Return i_1
 }
 Return i_2
}

iadd_sat_ N sx i_1 i_2 {
 If ((sx = U)) {
   Return $sat_u_(N, $int$((i_1 + i_2)))
 }
 Assert ((sx = S))
 Return $inv_signed_(N, $sat_s_(N, ($signed_(N, i_1) + $signed_(N, i_2))))
}

isub_sat_ N sx i_1 i_2 {
 If ((sx = U)) {
   Return $sat_u_(N, ($int$(i_1) - $int$(i_2)))
 }
 Assert ((sx = S))
 Return $inv_signed_(N, $sat_s_(N, ($signed_(N, i_1) - $signed_(N, i_2))))
}

packnum_ lanetype c {
 If (type(lanetype) == numtype) {
   Return c
 }
 Assert (type(lanetype) == packtype)
 Return $wrap__($size($unpack(lanetype)), $psize(lanetype), c)
}

unpacknum_ lanetype c {
 If (type(lanetype) == numtype) {
   Return c
 }
 Assert (type(lanetype) == packtype)
 Return $extend__($psize(lanetype), $size($unpack(lanetype)), U, c)
}

zeroop vcvtop {
 If (case(vcvtop) == EXTEND) {
   Return ?()
 }
 If (case(vcvtop) == CONVERT) {
   Return ?()
 }
 If (case(vcvtop) == TRUNC_SAT) {
   Let (TRUNC_SAT sx zero?{zero <- zero?}) = vcvtop
   Return zero?{zero <- zero?}
 }
 If (case(vcvtop) == DEMOTE) {
   Let (DEMOTE zero) = vcvtop
   Return ?(zero)
 }
 Assert ((vcvtop = (PROMOTELOW)))
 Return ?()
}

halfop vcvtop {
 If (case(vcvtop) == EXTEND) {
   Let (EXTEND half sx) = vcvtop
   Return ?(half)
 }
 If (case(vcvtop) == CONVERT) {
   Let (CONVERT half?{half <- half?} sx) = vcvtop
   Return half?{half <- half?}
 }
 If (case(vcvtop) == TRUNC_SAT) {
   Return ?()
 }
 If (case(vcvtop) == DEMOTE) {
   Return ?()
 }
 Assert ((vcvtop = (PROMOTELOW)))
 Return ?(LOW)
}

half half i j {
 If ((half = LOW)) {
   Return i
 }
 Assert ((half = HIGH))
 Return j
}

vvunop_ V128 NOT v128 {
 Return $inot_($size(V128), v128)
}

vvbinop_ V128 vvbinop v128_1 v128_2 {
 If ((vvbinop = AND)) {
   Return $iand_($size(V128), v128_1, v128_2)
 }
 If ((vvbinop = ANDNOT)) {
   Return $iandnot_($size(V128), v128_1, v128_2)
 }
 If ((vvbinop = OR)) {
   Return $ior_($size(V128), v128_1, v128_2)
 }
 Assert ((vvbinop = XOR))
 Return $ixor_($size(V128), v128_1, v128_2)
}

vvternop_ V128 BITSELECT v128_1 v128_2 v128_3 {
 Return $ibitselect_($size(V128), v128_1, v128_2, v128_3)
}

vunop_ (lanetype X M) vunop_ v128_1 {
 If (type(lanetype) == Jnn) {
   If ((vunop_ = ABS)) {
     Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
     Let v128 = $inv_lanes_((lanetype X M), $iabs_($lsizenn(lanetype), lane_1)*{lane_1 <- lane_1*})
     Return [v128]
   }
   If ((vunop_ = NEG)) {
     Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
     Let v128 = $inv_lanes_((lanetype X M), $ineg_($lsizenn(lanetype), lane_1)*{lane_1 <- lane_1*})
     Return [v128]
   }
   If ((vunop_ = POPCNT)) {
     Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
     Let v128 = $inv_lanes_((lanetype X M), $ipopcnt_($lsizenn(lanetype), lane_1)*{lane_1 <- lane_1*})
     Return [v128]
   }
 }
 Assert (type(lanetype) == Fnn)
 If ((vunop_ = ABS)) {
   Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
   Let lane*{lane <- lane*}*{lane* <- lane**} = $setproduct_(lane_((Fnn : Fnn <: lanetype)), $fabs_($sizenn(lanetype), lane_1)*{lane_1 <- lane_1*})
   Let v128*{v128 <- v128*} = $inv_lanes_((lanetype X M), lane*{lane <- lane*})*{lane* <- lane**}
   Return v128*{v128 <- v128*}
 }
 If ((vunop_ = NEG)) {
   Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
   Let lane*{lane <- lane*}*{lane* <- lane**} = $setproduct_(lane_((Fnn : Fnn <: lanetype)), $fneg_($sizenn(lanetype), lane_1)*{lane_1 <- lane_1*})
   Let v128*{v128 <- v128*} = $inv_lanes_((lanetype X M), lane*{lane <- lane*})*{lane* <- lane**}
   Return v128*{v128 <- v128*}
 }
 If ((vunop_ = SQRT)) {
   Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
   Let lane*{lane <- lane*}*{lane* <- lane**} = $setproduct_(lane_((Fnn : Fnn <: lanetype)), $fsqrt_($sizenn(lanetype), lane_1)*{lane_1 <- lane_1*})
   Let v128*{v128 <- v128*} = $inv_lanes_((lanetype X M), lane*{lane <- lane*})*{lane* <- lane**}
   Return v128*{v128 <- v128*}
 }
 If ((vunop_ = CEIL)) {
   Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
   Let lane*{lane <- lane*}*{lane* <- lane**} = $setproduct_(lane_((Fnn : Fnn <: lanetype)), $fceil_($sizenn(lanetype), lane_1)*{lane_1 <- lane_1*})
   Let v128*{v128 <- v128*} = $inv_lanes_((lanetype X M), lane*{lane <- lane*})*{lane* <- lane**}
   Return v128*{v128 <- v128*}
 }
 If ((vunop_ = FLOOR)) {
   Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
   Let lane*{lane <- lane*}*{lane* <- lane**} = $setproduct_(lane_((Fnn : Fnn <: lanetype)), $ffloor_($sizenn(lanetype), lane_1)*{lane_1 <- lane_1*})
   Let v128*{v128 <- v128*} = $inv_lanes_((lanetype X M), lane*{lane <- lane*})*{lane* <- lane**}
   Return v128*{v128 <- v128*}
 }
 If ((vunop_ = TRUNC)) {
   Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
   Let lane*{lane <- lane*}*{lane* <- lane**} = $setproduct_(lane_((Fnn : Fnn <: lanetype)), $ftrunc_($sizenn(lanetype), lane_1)*{lane_1 <- lane_1*})
   Let v128*{v128 <- v128*} = $inv_lanes_((lanetype X M), lane*{lane <- lane*})*{lane* <- lane**}
   Return v128*{v128 <- v128*}
 }
 Assert ((vunop_ = NEAREST))
 Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
 Let lane*{lane <- lane*}*{lane* <- lane**} = $setproduct_(lane_((Fnn : Fnn <: lanetype)), $fnearest_($sizenn(lanetype), lane_1)*{lane_1 <- lane_1*})
 Let v128*{v128 <- v128*} = $inv_lanes_((lanetype X M), lane*{lane <- lane*})*{lane* <- lane**}
 Return v128*{v128 <- v128*}
}

vbinop_ (lanetype X M) vbinop_ v128_1 v128_2 {
 If (type(lanetype) == Jnn) {
   If ((vbinop_ = ADD)) {
     Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
     Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
     Let v128 = $inv_lanes_((lanetype X M), $iadd_($lsizenn(lanetype), lane_1, lane_2)*{lane_1 <- lane_1*, lane_2 <- lane_2*})
     Return [v128]
   }
   If ((vbinop_ = SUB)) {
     Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
     Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
     Let v128 = $inv_lanes_((lanetype X M), $isub_($lsizenn(lanetype), lane_1, lane_2)*{lane_1 <- lane_1*, lane_2 <- lane_2*})
     Return [v128]
   }
   If (case(vbinop_) == MIN) {
     Let (MIN sx) = vbinop_
     Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
     Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
     Let v128 = $inv_lanes_((lanetype X M), $imin_($lsizenn(lanetype), sx, lane_1, lane_2)*{lane_1 <- lane_1*, lane_2 <- lane_2*})
     Return [v128]
   }
   If (case(vbinop_) == MAX) {
     Let (MAX sx) = vbinop_
     Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
     Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
     Let v128 = $inv_lanes_((lanetype X M), $imax_($lsizenn(lanetype), sx, lane_1, lane_2)*{lane_1 <- lane_1*, lane_2 <- lane_2*})
     Return [v128]
   }
   If (case(vbinop_) == ADD_SAT) {
     Let (ADD_SAT sx) = vbinop_
     Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
     Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
     Let v128 = $inv_lanes_((lanetype X M), $iadd_sat_($lsizenn(lanetype), sx, lane_1, lane_2)*{lane_1 <- lane_1*, lane_2 <- lane_2*})
     Return [v128]
   }
   If (case(vbinop_) == SUB_SAT) {
     Let (SUB_SAT sx) = vbinop_
     Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
     Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
     Let v128 = $inv_lanes_((lanetype X M), $isub_sat_($lsizenn(lanetype), sx, lane_1, lane_2)*{lane_1 <- lane_1*, lane_2 <- lane_2*})
     Return [v128]
   }
   If ((vbinop_ = MUL)) {
     Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
     Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
     Let v128 = $inv_lanes_((lanetype X M), $imul_($lsizenn(lanetype), lane_1, lane_2)*{lane_1 <- lane_1*, lane_2 <- lane_2*})
     Return [v128]
   }
   If ((vbinop_ = (AVGRU))) {
     Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
     Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
     Let v128 = $inv_lanes_((lanetype X M), $iavgr_($lsizenn(lanetype), U, lane_1, lane_2)*{lane_1 <- lane_1*, lane_2 <- lane_2*})
     Return [v128]
   }
   If ((vbinop_ = (Q15MULR_SATS))) {
     Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
     Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
     Let v128 = $inv_lanes_((lanetype X M), $iq15mulr_sat_($lsizenn(lanetype), S, lane_1, lane_2)*{lane_1 <- lane_1*, lane_2 <- lane_2*})
     Return [v128]
   }
 }
 Assert (type(lanetype) == Fnn)
 If ((vbinop_ = ADD)) {
   Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
   Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
   Let lane*{lane <- lane*}*{lane* <- lane**} = $setproduct_(lane_((Fnn : Fnn <: lanetype)), $fadd_($sizenn(lanetype), lane_1, lane_2)*{lane_1 <- lane_1*, lane_2 <- lane_2*})
   Let v128*{v128 <- v128*} = $inv_lanes_((lanetype X M), lane*{lane <- lane*})*{lane* <- lane**}
   Return v128*{v128 <- v128*}
 }
 If ((vbinop_ = SUB)) {
   Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
   Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
   Let lane*{lane <- lane*}*{lane* <- lane**} = $setproduct_(lane_((Fnn : Fnn <: lanetype)), $fsub_($sizenn(lanetype), lane_1, lane_2)*{lane_1 <- lane_1*, lane_2 <- lane_2*})
   Let v128*{v128 <- v128*} = $inv_lanes_((lanetype X M), lane*{lane <- lane*})*{lane* <- lane**}
   Return v128*{v128 <- v128*}
 }
 If ((vbinop_ = MUL)) {
   Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
   Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
   Let lane*{lane <- lane*}*{lane* <- lane**} = $setproduct_(lane_((Fnn : Fnn <: lanetype)), $fmul_($sizenn(lanetype), lane_1, lane_2)*{lane_1 <- lane_1*, lane_2 <- lane_2*})
   Let v128*{v128 <- v128*} = $inv_lanes_((lanetype X M), lane*{lane <- lane*})*{lane* <- lane**}
   Return v128*{v128 <- v128*}
 }
 If ((vbinop_ = DIV)) {
   Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
   Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
   Let lane*{lane <- lane*}*{lane* <- lane**} = $setproduct_(lane_((Fnn : Fnn <: lanetype)), $fdiv_($sizenn(lanetype), lane_1, lane_2)*{lane_1 <- lane_1*, lane_2 <- lane_2*})
   Let v128*{v128 <- v128*} = $inv_lanes_((lanetype X M), lane*{lane <- lane*})*{lane* <- lane**}
   Return v128*{v128 <- v128*}
 }
 If ((vbinop_ = MIN)) {
   Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
   Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
   Let lane*{lane <- lane*}*{lane* <- lane**} = $setproduct_(lane_((Fnn : Fnn <: lanetype)), $fmin_($sizenn(lanetype), lane_1, lane_2)*{lane_1 <- lane_1*, lane_2 <- lane_2*})
   Let v128*{v128 <- v128*} = $inv_lanes_((lanetype X M), lane*{lane <- lane*})*{lane* <- lane**}
   Return v128*{v128 <- v128*}
 }
 If ((vbinop_ = MAX)) {
   Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
   Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
   Let lane*{lane <- lane*}*{lane* <- lane**} = $setproduct_(lane_((Fnn : Fnn <: lanetype)), $fmax_($sizenn(lanetype), lane_1, lane_2)*{lane_1 <- lane_1*, lane_2 <- lane_2*})
   Let v128*{v128 <- v128*} = $inv_lanes_((lanetype X M), lane*{lane <- lane*})*{lane* <- lane**}
   Return v128*{v128 <- v128*}
 }
 If ((vbinop_ = PMIN)) {
   Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
   Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
   Let lane*{lane <- lane*}*{lane* <- lane**} = $setproduct_(lane_((Fnn : Fnn <: lanetype)), $fpmin_($sizenn(lanetype), lane_1, lane_2)*{lane_1 <- lane_1*, lane_2 <- lane_2*})
   Let v128*{v128 <- v128*} = $inv_lanes_((lanetype X M), lane*{lane <- lane*})*{lane* <- lane**}
   Return v128*{v128 <- v128*}
 }
 Assert ((vbinop_ = PMAX))
 Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
 Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
 Let lane*{lane <- lane*}*{lane* <- lane**} = $setproduct_(lane_((Fnn : Fnn <: lanetype)), $fpmax_($sizenn(lanetype), lane_1, lane_2)*{lane_1 <- lane_1*, lane_2 <- lane_2*})
 Let v128*{v128 <- v128*} = $inv_lanes_((lanetype X M), lane*{lane <- lane*})*{lane* <- lane**}
 Return v128*{v128 <- v128*}
}

vrelop_ (lanetype X M) vrelop_ v128_1 v128_2 {
 If (type(lanetype) == Jnn) {
   If ((vrelop_ = EQ)) {
     Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
     Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
     Let lane_3*{lane_3 <- lane_3*} = $extend__(1, $lsizenn(lanetype), S, $ieq_($lsizenn(lanetype), lane_1, lane_2))*{lane_1 <- lane_1*, lane_2 <- lane_2*}
     Let v128 = $inv_lanes_((lanetype X M), lane_3*{lane_3 <- lane_3*})
     Return v128
   }
   If ((vrelop_ = NE)) {
     Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
     Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
     Let lane_3*{lane_3 <- lane_3*} = $extend__(1, $lsizenn(lanetype), S, $ine_($lsizenn(lanetype), lane_1, lane_2))*{lane_1 <- lane_1*, lane_2 <- lane_2*}
     Let v128 = $inv_lanes_((lanetype X M), lane_3*{lane_3 <- lane_3*})
     Return v128
   }
   If (case(vrelop_) == LT) {
     Let (LT sx) = vrelop_
     Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
     Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
     Let lane_3*{lane_3 <- lane_3*} = $extend__(1, $lsizenn(lanetype), S, $ilt_($lsizenn(lanetype), sx, lane_1, lane_2))*{lane_1 <- lane_1*, lane_2 <- lane_2*}
     Let v128 = $inv_lanes_((lanetype X M), lane_3*{lane_3 <- lane_3*})
     Return v128
   }
   If (case(vrelop_) == GT) {
     Let (GT sx) = vrelop_
     Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
     Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
     Let lane_3*{lane_3 <- lane_3*} = $extend__(1, $lsizenn(lanetype), S, $igt_($lsizenn(lanetype), sx, lane_1, lane_2))*{lane_1 <- lane_1*, lane_2 <- lane_2*}
     Let v128 = $inv_lanes_((lanetype X M), lane_3*{lane_3 <- lane_3*})
     Return v128
   }
   If (case(vrelop_) == LE) {
     Let (LE sx) = vrelop_
     Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
     Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
     Let lane_3*{lane_3 <- lane_3*} = $extend__(1, $lsizenn(lanetype), S, $ile_($lsizenn(lanetype), sx, lane_1, lane_2))*{lane_1 <- lane_1*, lane_2 <- lane_2*}
     Let v128 = $inv_lanes_((lanetype X M), lane_3*{lane_3 <- lane_3*})
     Return v128
   }
   If (case(vrelop_) == GE) {
     Let (GE sx) = vrelop_
     Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
     Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
     Let lane_3*{lane_3 <- lane_3*} = $extend__(1, $lsizenn(lanetype), S, $ige_($lsizenn(lanetype), sx, lane_1, lane_2))*{lane_1 <- lane_1*, lane_2 <- lane_2*}
     Let v128 = $inv_lanes_((lanetype X M), lane_3*{lane_3 <- lane_3*})
     Return v128
   }
 }
 Assert (type(lanetype) == Fnn)
 If ((vrelop_ = EQ)) {
   Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
   Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
   Let Inn = $isize^-1($size(lanetype))
   Let lane_3*{lane_3 <- lane_3*} = $extend__(1, $sizenn(lanetype), S, $feq_($sizenn(lanetype), lane_1, lane_2))*{lane_1 <- lane_1*, lane_2 <- lane_2*}
   Let v128 = $inv_lanes_((Inn X M), lane_3*{lane_3 <- lane_3*})
   Return v128
 }
 If ((vrelop_ = NE)) {
   Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
   Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
   Let Inn = $isize^-1($size(lanetype))
   Let lane_3*{lane_3 <- lane_3*} = $extend__(1, $sizenn(lanetype), S, $fne_($sizenn(lanetype), lane_1, lane_2))*{lane_1 <- lane_1*, lane_2 <- lane_2*}
   Let v128 = $inv_lanes_((Inn X M), lane_3*{lane_3 <- lane_3*})
   Return v128
 }
 If ((vrelop_ = LT)) {
   Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
   Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
   Let Inn = $isize^-1($size(lanetype))
   Let lane_3*{lane_3 <- lane_3*} = $extend__(1, $sizenn(lanetype), S, $flt_($sizenn(lanetype), lane_1, lane_2))*{lane_1 <- lane_1*, lane_2 <- lane_2*}
   Let v128 = $inv_lanes_((Inn X M), lane_3*{lane_3 <- lane_3*})
   Return v128
 }
 If ((vrelop_ = GT)) {
   Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
   Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
   Let Inn = $isize^-1($size(lanetype))
   Let lane_3*{lane_3 <- lane_3*} = $extend__(1, $sizenn(lanetype), S, $fgt_($sizenn(lanetype), lane_1, lane_2))*{lane_1 <- lane_1*, lane_2 <- lane_2*}
   Let v128 = $inv_lanes_((Inn X M), lane_3*{lane_3 <- lane_3*})
   Return v128
 }
 If ((vrelop_ = LE)) {
   Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
   Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
   Let Inn = $isize^-1($size(lanetype))
   Let lane_3*{lane_3 <- lane_3*} = $extend__(1, $sizenn(lanetype), S, $fle_($sizenn(lanetype), lane_1, lane_2))*{lane_1 <- lane_1*, lane_2 <- lane_2*}
   Let v128 = $inv_lanes_((Inn X M), lane_3*{lane_3 <- lane_3*})
   Return v128
 }
 Assert ((vrelop_ = GE))
 Let lane_1*{lane_1 <- lane_1*} = $lanes_((lanetype X M), v128_1)
 Let lane_2*{lane_2 <- lane_2*} = $lanes_((lanetype X M), v128_2)
 Let Inn = $isize^-1($size(lanetype))
 Let lane_3*{lane_3 <- lane_3*} = $extend__(1, $sizenn(lanetype), S, $fge_($sizenn(lanetype), lane_1, lane_2))*{lane_1 <- lane_1*, lane_2 <- lane_2*}
 Let v128 = $inv_lanes_((Inn X M), lane_3*{lane_3 <- lane_3*})
 Return v128
}

vcvtop__ (lanetype' X M_1) (lanetype X M_2) vcvtop iN_1 {
 If (type(lanetype') == Jnn) {
   If ((type(lanetype) == Jnn /\ case(vcvtop) == EXTEND)) {
     Let (EXTEND half sx) = vcvtop
     Let iN_2 = $extend__($lsizenn1(lanetype'), $lsizenn2(lanetype), sx, iN_1)
     Return [iN_2]
   }
   If ((type(lanetype) == Fnn /\ case(vcvtop) == CONVERT)) {
     Let (CONVERT half?{half <- half?} sx) = vcvtop
     Let fN_2 = $convert__($lsizenn1(lanetype'), $lsizenn2(lanetype), sx, iN_1)
     Return [fN_2]
   }
 }
 Assert (type(lanetype') == Fnn)
 If ((type(lanetype) == Inn /\ case(vcvtop) == TRUNC_SAT)) {
   Let (TRUNC_SAT sx zero?{zero <- zero?}) = vcvtop
   Let iN_2?{iN_2 <- iN_2?} = $trunc_sat__($lsizenn1(lanetype'), $lsizenn2(lanetype), sx, iN_1)
   Return $list_(lane_((Inn_2 : Inn <: lanetype)), iN_2?{iN_2 <- iN_2?})
 }
 Assert (type(lanetype) == Fnn)
 If ((vcvtop = (DEMOTE ZERO))) {
   Let fN_2*{fN_2 <- fN_2*} = $demote__($lsizenn1(lanetype'), $lsizenn2(lanetype), iN_1)
   Return fN_2*{fN_2 <- fN_2*}
 }
 Assert ((vcvtop = (PROMOTELOW)))
 Let fN_2*{fN_2 <- fN_2*} = $promote__($lsizenn1(lanetype'), $lsizenn2(lanetype), iN_1)
 Return fN_2*{fN_2 <- fN_2*}
}

vextunop__ (Inn_1 X M_1) (Inn_2 X M_2) (EXTADD_PAIRWISE sx) c_1 {
 Let ci*{ci <- ci*} = $lanes_((Inn_2 X M_2), c_1)
 Let [cj_1, cj_2]*{cj_1 <- cj_1*, cj_2 <- cj_2*} = $concat__1^-1(iN($lsizenn1((Inn_1 : Inn <: lanetype))), $extend__($lsizenn2(Inn_2), $lsizenn1(Inn_1), sx, ci)*{ci <- ci*})
 Let c = $inv_lanes_((Inn_1 X M_1), $iadd_($lsizenn1(Inn_1), cj_1, cj_2)*{cj_1 <- cj_1*, cj_2 <- cj_2*})
 Return c
}

vextbinop__ (Inn_1 X M_1) (Inn_2 X M_2) vextbinop_ c_1 c_2 {
 If (case(vextbinop_) == EXTMUL) {
   Let (EXTMUL half sx) = vextbinop_
   Let ci_1*{ci_1 <- ci_1*} = $lanes_((Inn_2 X M_2), c_1)[$half(half, 0, M_1) : M_1]
   Let ci_2*{ci_2 <- ci_2*} = $lanes_((Inn_2 X M_2), c_2)[$half(half, 0, M_1) : M_1]
   Let c = $inv_lanes_((Inn_1 X M_1), $imul_($lsizenn1(Inn_1), $extend__($lsizenn2(Inn_2), $lsizenn1(Inn_1), sx, ci_1), $extend__($lsizenn2(Inn_2), $lsizenn1(Inn_1), sx, ci_2))*{ci_1 <- ci_1*, ci_2 <- ci_2*})
   Return c
 }
 Assert ((vextbinop_ = (DOTS)))
 Let ci_1*{ci_1 <- ci_1*} = $lanes_((Inn_2 X M_2), c_1)
 Let ci_2*{ci_2 <- ci_2*} = $lanes_((Inn_2 X M_2), c_2)
 Let [cj_1, cj_2]*{cj_1 <- cj_1*, cj_2 <- cj_2*} = $concat__1^-1(iN($lsizenn1((Inn_1 : Inn <: lanetype))), $imul_($lsizenn1(Inn_1), $extend__($lsizenn2(Inn_2), $lsizenn1(Inn_1), S, ci_1), $extend__($lsizenn2(Inn_2), $lsizenn1(Inn_1), S, ci_2))*{ci_1 <- ci_1*, ci_2 <- ci_2*})
 Let c = $inv_lanes_((Inn_1 X M_1), $iadd_($lsizenn1(Inn_1), cj_1, cj_2)*{cj_1 <- cj_1*, cj_2 <- cj_2*})
 Return c
}

vshiftop_ (Jnn X M) vshiftop_ lane n {
 If ((vshiftop_ = SHL)) {
   Return $ishl_($lsizenn(Jnn), lane, n)
 }
 Assert (case(vshiftop_) == SHR)
 Let (SHR sx) = vshiftop_
 Return $ishr_($lsizenn(Jnn), sx, lane, n)
}

default_ valtype {
 If ((valtype = I32)) {
   Return (I32.CONST 0)
 }
 If ((valtype = I64)) {
   Return (I64.CONST 0)
 }
 If ((valtype = F32)) {
   Return (F32.CONST $fzero(32))
 }
 If ((valtype = F64)) {
   Return (F64.CONST $fzero(64))
 }
 If ((valtype = V128)) {
   Return (V128.CONST 0)
 }
 If ((valtype = FUNCREF)) {
   Return (REF.NULL FUNCREF)
 }
 If ((valtype = EXTERNREF)) {
   Return (REF.NULL EXTERNREF)
 }
 Fail
}

funcsxa externaddr'*{externaddr' <- externaddr'} {
 If ((externaddr'*{externaddr' <- externaddr'} = [])) {
   Return []
 }
 Let [externaddr_0] :: xv*{xv <- xv*} = externaddr'*{externaddr' <- externaddr'}
 If (case(externaddr_0) == FUNC) {
   Let (FUNC fa) = externaddr_0
   Return [fa] :: $funcsxa(xv*{xv <- xv*})
 }
 Let [externaddr] :: xv*{xv <- xv*} = externaddr'*{externaddr' <- externaddr'}
 Return $funcsxa(xv*{xv <- xv*})
}

globalsxa externaddr'*{externaddr' <- externaddr'} {
 If ((externaddr'*{externaddr' <- externaddr'} = [])) {
   Return []
 }
 Let [externaddr_0] :: xv*{xv <- xv*} = externaddr'*{externaddr' <- externaddr'}
 If (case(externaddr_0) == GLOBAL) {
   Let (GLOBAL ga) = externaddr_0
   Return [ga] :: $globalsxa(xv*{xv <- xv*})
 }
 Let [externaddr] :: xv*{xv <- xv*} = externaddr'*{externaddr' <- externaddr'}
 Return $globalsxa(xv*{xv <- xv*})
}

tablesxa externaddr'*{externaddr' <- externaddr'} {
 If ((externaddr'*{externaddr' <- externaddr'} = [])) {
   Return []
 }
 Let [externaddr_0] :: xv*{xv <- xv*} = externaddr'*{externaddr' <- externaddr'}
 If (case(externaddr_0) == TABLE) {
   Let (TABLE ta) = externaddr_0
   Return [ta] :: $tablesxa(xv*{xv <- xv*})
 }
 Let [externaddr] :: xv*{xv <- xv*} = externaddr'*{externaddr' <- externaddr'}
 Return $tablesxa(xv*{xv <- xv*})
}

memsxa externaddr'*{externaddr' <- externaddr'} {
 If ((externaddr'*{externaddr' <- externaddr'} = [])) {
   Return []
 }
 Let [externaddr_0] :: xv*{xv <- xv*} = externaddr'*{externaddr' <- externaddr'}
 If (case(externaddr_0) == MEM) {
   Let (MEM ma) = externaddr_0
   Return [ma] :: $memsxa(xv*{xv <- xv*})
 }
 Let [externaddr] :: xv*{xv <- xv*} = externaddr'*{externaddr' <- externaddr'}
 Return $memsxa(xv*{xv <- xv*})
}

store (s, f) {
 Return
}

frame (s, f) {
 Return f
}

funcaddr (s, f) {
 Return f.MODULE.FUNCS
}

funcinst (s, f) {
 Return s.FUNCS
}

globalinst (s, f) {
 Return s.GLOBALS
}

tableinst (s, f) {
 Return s.TABLES
}

meminst (s, f) {
 Return s.MEMS
}

eleminst (s, f) {
 Return s.ELEMS
}

datainst (s, f) {
 Return s.DATAS
}

moduleinst (s, f) {
 Return f.MODULE
}

type (s, f) x {
 Return f.MODULE.TYPES[x]
}

func (s, f) x {
 Return s.FUNCS[f.MODULE.FUNCS[x]]
}

global (s, f) x {
 Return s.GLOBALS[f.MODULE.GLOBALS[x]]
}

table (s, f) x {
 Return s.TABLES[f.MODULE.TABLES[x]]
}

mem (s, f) x {
 Return s.MEMS[f.MODULE.MEMS[x]]
}

elem (s, f) x {
 Return s.ELEMS[f.MODULE.ELEMS[x]]
}

data (s, f) x {
 Return s.DATAS[f.MODULE.DATAS[x]]
}

local (s, f) x {
 Return f.LOCALS[x]
}

with_local (s, f) x v {
 f.LOCALS[x] := v
}

with_global (s, f) x v {
 s.GLOBALS[f.MODULE.GLOBALS[x]].VALUE := v
}

with_table (s, f) x i r {
 s.TABLES[f.MODULE.TABLES[x]].REFS[i] := r
}

with_tableinst (s, f) x ti {
 s.TABLES[f.MODULE.TABLES[x]] := ti
}

with_mem (s, f) x i j b*{b <- b*} {
 s.MEMS[f.MODULE.MEMS[x]].BYTES[i : j] := b*{b <- b*}
}

with_meminst (s, f) x mi {
 s.MEMS[f.MODULE.MEMS[x]] := mi
}

with_elem (s, f) x r*{r <- r*} {
 s.ELEMS[f.MODULE.ELEMS[x]].REFS := r*{r <- r*}
}

with_data (s, f) x b*{b <- b*} {
 s.DATAS[f.MODULE.DATAS[x]].BYTES := b*{b <- b*}
}

growtable ti n r {
 Let { TYPE: (([ i .. j?{j <- j?} ]) rt); REFS: r'*{r' <- r'*}; } = ti
 Let i' = (|r'*{r' <- r'*}| + n)
 If ((i' <= j)?{j <- j?}) {
   Let ti' = { TYPE: (([ i' .. j?{j <- j?} ]) rt); REFS: r'*{r' <- r'*} :: r^n{}; }
   Return ti'
 }
 Fail
}

growmemory mi n {
 Let { TYPE: (([ i .. j?{j <- j?} ]) PAGE); BYTES: b*{b <- b*}; } = mi
 Let i' = (($rat$(|b*{b <- b*}|) / $rat$((64 * $Ki()))) + $rat$(n))
 If ((i' <= $rat$(j))?{j <- j?}) {
   Let mi' = { TYPE: (([ $nat$(i') .. j?{j <- j?} ]) PAGE); BYTES: b*{b <- b*} :: 0^(n * (64 * $Ki())){}; }
   Return mi'
 }
 Fail
}

blocktype z blocktype {
 If ((blocktype = (_RESULT ?()))) {
   Return ([] -> [])
 }
 If (case(blocktype) == _RESULT) {
   Let (_RESULT valtype_0?{valtype_0 <- valtype_0?}) = blocktype
   If (valtype_0?{valtype_0 <- valtype_0?} != None) {
     Let ?(t) = valtype_0?{valtype_0 <- valtype_0?}
     Return ([] -> [t])
   }
 }
 Assert (case(blocktype) == _IDX)
 Let (_IDX x) = blocktype
 Return $type(z, x)
}

funcs externaddr''*{externaddr'' <- externaddr''} {
 If ((externaddr''*{externaddr'' <- externaddr''} = [])) {
   Return []
 }
 Let [externaddr_0] :: externaddr'*{externaddr' <- externaddr'*} = externaddr''*{externaddr'' <- externaddr''}
 If (case(externaddr_0) == FUNC) {
   Let (FUNC fa) = externaddr_0
   Return [fa] :: $funcs(externaddr'*{externaddr' <- externaddr'*})
 }
 Let [externaddr] :: externaddr'*{externaddr' <- externaddr'*} = externaddr''*{externaddr'' <- externaddr''}
 Return $funcs(externaddr'*{externaddr' <- externaddr'*})
}

globals externaddr''*{externaddr'' <- externaddr''} {
 If ((externaddr''*{externaddr'' <- externaddr''} = [])) {
   Return []
 }
 Let [externaddr_0] :: externaddr'*{externaddr' <- externaddr'*} = externaddr''*{externaddr'' <- externaddr''}
 If (case(externaddr_0) == GLOBAL) {
   Let (GLOBAL ga) = externaddr_0
   Return [ga] :: $globals(externaddr'*{externaddr' <- externaddr'*})
 }
 Let [externaddr] :: externaddr'*{externaddr' <- externaddr'*} = externaddr''*{externaddr'' <- externaddr''}
 Return $globals(externaddr'*{externaddr' <- externaddr'*})
}

tables externaddr''*{externaddr'' <- externaddr''} {
 If ((externaddr''*{externaddr'' <- externaddr''} = [])) {
   Return []
 }
 Let [externaddr_0] :: externaddr'*{externaddr' <- externaddr'*} = externaddr''*{externaddr'' <- externaddr''}
 If (case(externaddr_0) == TABLE) {
   Let (TABLE ta) = externaddr_0
   Return [ta] :: $tables(externaddr'*{externaddr' <- externaddr'*})
 }
 Let [externaddr] :: externaddr'*{externaddr' <- externaddr'*} = externaddr''*{externaddr'' <- externaddr''}
 Return $tables(externaddr'*{externaddr' <- externaddr'*})
}

mems externaddr''*{externaddr'' <- externaddr''} {
 If ((externaddr''*{externaddr'' <- externaddr''} = [])) {
   Return []
 }
 Let [externaddr_0] :: externaddr'*{externaddr' <- externaddr'*} = externaddr''*{externaddr'' <- externaddr''}
 If (case(externaddr_0) == MEM) {
   Let (MEM ma) = externaddr_0
   Return [ma] :: $mems(externaddr'*{externaddr' <- externaddr'*})
 }
 Let [externaddr] :: externaddr'*{externaddr' <- externaddr'*} = externaddr''*{externaddr'' <- externaddr''}
 Return $mems(externaddr'*{externaddr' <- externaddr'*})
}

allocfunc s moduleinst func {
 Let (FUNC x local*{local <- local*} expr) = func
 Let fi = { TYPE: moduleinst.TYPES[x]; MODULE: moduleinst; CODE: func; }
 Let a = |s.FUNCS|
 fi :+ s.FUNCS
 Return a
}

allocfuncs s moduleinst func''*{func'' <- func''} {
 If ((func''*{func'' <- func''} = [])) {
   Return []
 }
 Let [func] :: func'*{func' <- func'*} = func''*{func'' <- func''}
 Let fa = $allocfunc(s, moduleinst, func)
 Let fa'*{fa' <- fa'*} = $allocfuncs(s, moduleinst, func'*{func' <- func'*})
 Return [fa] :: fa'*{fa' <- fa'*}
}

allocglobal s globaltype val {
 Let gi = { TYPE: globaltype; VALUE: val; }
 Let a = |s.GLOBALS|
 gi :+ s.GLOBALS
 Return a
}

allocglobals s globaltype''*{globaltype'' <- globaltype''} val''*{val'' <- val''} {
 If ((globaltype''*{globaltype'' <- globaltype''} = [])) {
   Assert ((val''*{val'' <- val''} = []))
   Return []
 }
 Else {
   Let [globaltype] :: globaltype'*{globaltype' <- globaltype'*} = globaltype''*{globaltype'' <- globaltype''}
   Assert ((|val''*{val'' <- val''}| >= 1))
   Let [val] :: val'*{val' <- val'*} = val''*{val'' <- val''}
   Let ga = $allocglobal(s, globaltype, val)
   Let ga'*{ga' <- ga'*} = $allocglobals(s, globaltype'*{globaltype' <- globaltype'*}, val'*{val' <- val'*})
   Return [ga] :: ga'*{ga' <- ga'*}
 }
}

alloctable s (([ i .. j?{j <- j?} ]) rt) {
 Let ti = { TYPE: (([ i .. j?{j <- j?} ]) rt); REFS: (REF.NULL rt)^i{}; }
 Let a = |s.TABLES|
 ti :+ s.TABLES
 Return a
}

alloctables s tabletype''*{tabletype'' <- tabletype''} {
 If ((tabletype''*{tabletype'' <- tabletype''} = [])) {
   Return []
 }
 Let [tabletype] :: tabletype'*{tabletype' <- tabletype'*} = tabletype''*{tabletype'' <- tabletype''}
 Let ta = $alloctable(s, tabletype)
 Let ta'*{ta' <- ta'*} = $alloctables(s, tabletype'*{tabletype' <- tabletype'*})
 Return [ta] :: ta'*{ta' <- ta'*}
}

allocmem s (([ i .. j?{j <- j?} ]) PAGE) {
 Let mi = { TYPE: (([ i .. j?{j <- j?} ]) PAGE); BYTES: 0^(i * (64 * $Ki())){}; }
 Let a = |s.MEMS|
 mi :+ s.MEMS
 Return a
}

allocmems s memtype''*{memtype'' <- memtype''} {
 If ((memtype''*{memtype'' <- memtype''} = [])) {
   Return []
 }
 Let [memtype] :: memtype'*{memtype' <- memtype'*} = memtype''*{memtype'' <- memtype''}
 Let ma = $allocmem(s, memtype)
 Let ma'*{ma' <- ma'*} = $allocmems(s, memtype'*{memtype' <- memtype'*})
 Return [ma] :: ma'*{ma' <- ma'*}
}

allocelem s rt ref*{ref <- ref*} {
 Let ei = { TYPE: rt; REFS: ref*{ref <- ref*}; }
 Let a = |s.ELEMS|
 ei :+ s.ELEMS
 Return a
}

allocelems s reftype*{reftype <- reftype} ref''*{ref'' <- ref''} {
 If ((ref''*{ref'' <- ref''} = [])) {
   Assert ((reftype*{reftype <- reftype} = []))
   Return []
 }
 Else {
   Let [ref*{ref <- ref*}] :: ref'*{ref' <- ref'*}*{ref'* <- ref'**} = ref''*{ref'' <- ref''}
   Assert ((|reftype*{reftype <- reftype}| >= 1))
   Let [rt] :: rt'*{rt' <- rt'*} = reftype*{reftype <- reftype}
   Let ea = $allocelem(s, rt, ref*{ref <- ref*})
   Let ea'*{ea' <- ea'*} = $allocelems(s, rt'*{rt' <- rt'*}, ref'*{ref' <- ref'*}*{ref'* <- ref'**})
   Return [ea] :: ea'*{ea' <- ea'*}
 }
}

allocdata s byte*{byte <- byte*} {
 Let di = { BYTES: byte*{byte <- byte*}; }
 Let a = |s.DATAS|
 di :+ s.DATAS
 Return a
}

allocdatas s byte''*{byte'' <- byte''} {
 If ((byte''*{byte'' <- byte''} = [])) {
   Return []
 }
 Let [byte*{byte <- byte*}] :: byte'*{byte' <- byte'*}*{byte'* <- byte'**} = byte''*{byte'' <- byte''}
 Let da = $allocdata(s, byte*{byte <- byte*})
 Let da'*{da' <- da'*} = $allocdatas(s, byte'*{byte' <- byte'*}*{byte'* <- byte'**})
 Return [da] :: da'*{da' <- da'*}
}

instexport fa*{fa <- fa*} ga*{ga <- ga*} ta*{ta <- ta*} ma*{ma <- ma*} (EXPORT name externidx) {
 If (case(externidx) == FUNC) {
   Let (FUNC x) = externidx
   Return { NAME: name; ADDR: (FUNC fa*{fa <- fa*}[x]); }
 }
 If (case(externidx) == GLOBAL) {
   Let (GLOBAL x) = externidx
   Return { NAME: name; ADDR: (GLOBAL ga*{ga <- ga*}[x]); }
 }
 If (case(externidx) == TABLE) {
   Let (TABLE x) = externidx
   Return { NAME: name; ADDR: (TABLE ta*{ta <- ta*}[x]); }
 }
 Assert (case(externidx) == MEM)
 Let (MEM x) = externidx
 Return { NAME: name; ADDR: (MEM ma*{ma <- ma*}[x]); }
}

allocmodule s module externaddr*{externaddr <- externaddr*} val*{val <- val*} ref*{ref <- ref*}*{ref* <- ref**} {
 Let (MODULE type_0*{type_0 <- type_0*} import*{import <- import*} func^n_func{func <- func*} global_1*{global_1 <- global_1*} table_2*{table_2 <- table_2*} mem_3*{mem_3 <- mem_3*} elem_4*{elem_4 <- elem_4*} data_5*{data_5 <- data_5*} start?{start <- start?} export*{export <- export*}) = module
 Let (DATA byte*{byte <- byte*} datamode)^n_data{byte* <- byte**, datamode <- datamode*} = data_5*{data_5 <- data_5*}
 Let (ELEM rt expr_2*{expr_2 <- expr_2*} elemmode)^n_elem{elemmode <- elemmode*, expr_2* <- expr_2**, rt <- rt*} = elem_4*{elem_4 <- elem_4*}
 Let (MEMORY memtype)^n_mem{memtype <- memtype*} = mem_3*{mem_3 <- mem_3*}
 Let (TABLE tabletype)^n_table{tabletype <- tabletype*} = table_2*{table_2 <- table_2*}
 Let (GLOBAL globaltype expr_1)^n_global{expr_1 <- expr_1*, globaltype <- globaltype*} = global_1*{global_1 <- global_1*}
 Let (TYPE ft)*{ft <- ft*} = type_0*{type_0 <- type_0*}
 Let fa_ex*{fa_ex <- fa_ex*} = $funcs(externaddr*{externaddr <- externaddr*})
 Let ga_ex*{ga_ex <- ga_ex*} = $globals(externaddr*{externaddr <- externaddr*})
 Let ma_ex*{ma_ex <- ma_ex*} = $mems(externaddr*{externaddr <- externaddr*})
 Let ta_ex*{ta_ex <- ta_ex*} = $tables(externaddr*{externaddr <- externaddr*})
 Let fa*{fa <- fa*} = (|s.FUNCS| + i_func)^(i_func<n_func){}
 Let ga*{ga <- ga*} = (|s.GLOBALS| + i_global)^(i_global<n_global){}
 Let ta*{ta <- ta*} = (|s.TABLES| + i_table)^(i_table<n_table){}
 Let ma*{ma <- ma*} = (|s.MEMS| + i_mem)^(i_mem<n_mem){}
 Let ea*{ea <- ea*} = (|s.ELEMS| + i_elem)^(i_elem<n_elem){}
 Let da*{da <- da*} = (|s.DATAS| + i_data)^(i_data<n_data){}
 Let xi*{xi <- xi*} = $instexport(fa_ex*{fa_ex <- fa_ex*} :: fa*{fa <- fa*}, ga_ex*{ga_ex <- ga_ex*} :: ga*{ga <- ga*}, ta_ex*{ta_ex <- ta_ex*} :: ta*{ta <- ta*}, ma_ex*{ma_ex <- ma_ex*} :: ma*{ma <- ma*}, export)*{export <- export*}
 Let moduleinst = { TYPES: ft*{ft <- ft*}; FUNCS: fa_ex*{fa_ex <- fa_ex*} :: fa*{fa <- fa*}; GLOBALS: ga_ex*{ga_ex <- ga_ex*} :: ga*{ga <- ga*}; TABLES: ta_ex*{ta_ex <- ta_ex*} :: ta*{ta <- ta*}; MEMS: ma_ex*{ma_ex <- ma_ex*} :: ma*{ma <- ma*}; ELEMS: ea*{ea <- ea*}; DATAS: da*{da <- da*}; EXPORTS: xi*{xi <- xi*}; }
 Let funcaddr_0*{funcaddr_0 <- funcaddr_0*} = $allocfuncs(s, moduleinst, func^n_func{func <- func*})
 Assert ((funcaddr_0*{funcaddr_0 <- funcaddr_0*} = fa*{fa <- fa*}))
 Let globaladdr_0*{globaladdr_0 <- globaladdr_0*} = $allocglobals(s, globaltype^n_global{globaltype <- globaltype*}, val*{val <- val*})
 Assert ((globaladdr_0*{globaladdr_0 <- globaladdr_0*} = ga*{ga <- ga*}))
 Let tableaddr_0*{tableaddr_0 <- tableaddr_0*} = $alloctables(s, tabletype^n_table{tabletype <- tabletype*})
 Assert ((tableaddr_0*{tableaddr_0 <- tableaddr_0*} = ta*{ta <- ta*}))
 Let memaddr_0*{memaddr_0 <- memaddr_0*} = $allocmems(s, memtype^n_mem{memtype <- memtype*})
 Assert ((memaddr_0*{memaddr_0 <- memaddr_0*} = ma*{ma <- ma*}))
 Let elemaddr_0*{elemaddr_0 <- elemaddr_0*} = $allocelems(s, rt^n_elem{rt <- rt*}, ref*{ref <- ref*}*{ref* <- ref**})
 Assert ((elemaddr_0*{elemaddr_0 <- elemaddr_0*} = ea*{ea <- ea*}))
 Let dataaddr_0*{dataaddr_0 <- dataaddr_0*} = $allocdatas(s, byte*{byte <- byte*}^n_data{byte* <- byte**})
 Assert ((dataaddr_0*{dataaddr_0 <- dataaddr_0*} = da*{da <- da*}))
 Return moduleinst
}

runelem (ELEM reftype expr*{expr <- expr*} elemmode) i {
 If ((elemmode = PASSIVE)) {
   Return []
 }
 If ((elemmode = DECLARE)) {
   Return [(ELEM.DROP i)]
 }
 Assert (case(elemmode) == ACTIVE)
 Let (ACTIVE x instr*{instr <- instr*}) = elemmode
 Let n = |expr*{expr <- expr*}|
 Return instr*{instr <- instr*} :: [(I32.CONST 0), (I32.CONST n), (TABLE.INIT x i), (ELEM.DROP i)]
}

rundata (DATA byte*{byte <- byte*} datamode) i {
 If ((datamode = PASSIVE)) {
   Return []
 }
 Assert (case(datamode) == ACTIVE)
 Let (ACTIVE memidx_0 instr*{instr <- instr*}) = datamode
 Assert ((memidx_0 = 0))
 Let n = |byte*{byte <- byte*}|
 Return instr*{instr <- instr*} :: [(I32.CONST 0), (I32.CONST n), (MEMORY.INIT i), (DATA.DROP i)]
}

instantiate s module externaddr*{externaddr <- externaddr*} {
 Let (MODULE type*{type <- type*} import*{import <- import*} func*{func <- func*} global*{global <- global*} table*{table <- table*} mem*{mem <- mem*} elem*{elem <- elem*} data*{data <- data*} start?{start <- start?} export*{export <- export*}) = module
 Let (TYPE functype)*{functype <- functype*} = type*{type <- type*}
 Let n_D = |data*{data <- data*}|
 Let n_E = |elem*{elem <- elem*}|
 Let n_F = |func*{func <- func*}|
 Let (GLOBAL globaltype expr_G)*{expr_G <- expr_G*, globaltype <- globaltype*} = global*{global <- global*}
 Let (ELEM reftype expr_E*{expr_E <- expr_E*} elemmode)*{elemmode <- elemmode*, expr_E* <- expr_E**, reftype <- reftype*} = elem*{elem <- elem*}
 Let instr_D*{instr_D <- instr_D*} = $concat_(instr, $rundata(data*{data <- data*}[j], j)^(j<n_D){})
 Let instr_E*{instr_E <- instr_E*} = $concat_(instr, $runelem(elem*{elem <- elem*}[i], i)^(i<n_E){})
 Let moduleinst_init = { TYPES: functype*{functype <- functype*}; FUNCS: $funcs(externaddr*{externaddr <- externaddr*}) :: (|s.FUNCS| + i_F)^(i_F<n_F){}; GLOBALS: $globals(externaddr*{externaddr <- externaddr*}); TABLES: []; MEMS: []; ELEMS: []; DATAS: []; EXPORTS: []; }
 Let f_init = { LOCALS: []; MODULE: moduleinst_init; }
 Let z = (s, f_init)
 Push (FRAME_ 0 { $frame(z) })
 Let [val]*{val <- val*} = $Eval_expr(z, expr_G)*{expr_G <- expr_G*}
 Let [ref]*{ref <- ref*}*{ref* <- ref**} = $Eval_expr(z, expr_E)*{expr_E <- expr_E*}*{expr_E* <- expr_E**}
 Pop (FRAME_ 0 { $frame(z) })
 Let moduleinst = $allocmodule(s, module, externaddr*{externaddr <- externaddr*}, val*{val <- val*}, ref*{ref <- ref*}*{ref* <- ref**})
 Let f = { LOCALS: []; MODULE: moduleinst; }
 Push (FRAME_ 0 { f })
 Execute instr_E*{instr_E <- instr_E*}
 Execute instr_D*{instr_D <- instr_D*}
 If (start?{start <- start?} != None) {
   Let ?((START x)) = start?{start <- start?}
   Let instr_0 = (CALL x)
   Execute instr_0
 }
 Pop (FRAME_ 0 { f })
 Return f.MODULE
}

invoke s fa val^n{val <- val*} {
 Let f = { LOCALS: []; MODULE: { TYPES: []; FUNCS: []; GLOBALS: []; TABLES: []; MEMS: []; ELEMS: []; DATAS: []; EXPORTS: []; }; }
 Push (FRAME_ 0 { (s, f) })
 Let (t_1^n{t_1 <- t_1*} -> t_2*{t_2 <- t_2*}) = $funcinst((s, f))[fa].TYPE
 Pop (FRAME_ 0 { _f })
 Let k = |t_2*{t_2 <- t_2*}|
 Push (FRAME_ k { f })
 Push val^n{val <- val*}
 Execute (CALL_ADDR fa)
 Pop val'^k{val' <- val'*}
 Pop (FRAME_ k { f })
 Return val'^k{val' <- val'*}
}

Eval_expr instr*{instr <- instr*} {
 Execute instr*{instr <- instr*}
 Pop val
 Return [val]
}

