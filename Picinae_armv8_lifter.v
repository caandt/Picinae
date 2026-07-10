Require Import Picinae_armv8_pcode.
Require Import List String Ascii NArith Bool.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope N_scope.

Module Notation.
  Definition shift_add n (b: bool) :=
    match n with
    | N0 => if b then Npos xH else N0
    | Npos p => if b then Npos (xI p) else Npos (xO p)
    end.
  Compute match "ae" with | "ab" => true | _ => false end.
  Definition parse_pattern pat :=
    let (s, e) := match pat with
                    | String "!" (String "=" s') => (s', false)
                    | _ => (pat, true)
                    end in
    ((fix F s val mask :=
      match s with
      | EmptyString => (val, mask)
      | String c s' =>
          match c with
          | "1" => F s' (shift_add val true)  (shift_add mask true)
          | "0" => F s' (shift_add val false) (shift_add mask true)
          | "x" => F s' (shift_add val false) (shift_add mask false)
          | "-" => (0, 0)
          | _   => F s' val mask
          end%char
      end) s 0 0, e).
  Definition rev_str s :=
    (fix F s1 s2 :=
      match s1 with
      | EmptyString => s2
      | String c s' => F s' (String c s2)
      end) s "".
  Fixpoint split_str s curr :=
    match s with
    | EmptyString =>
        match curr with
        | EmptyString => []
        | _ => [rev_str curr]
        end
    | String c s' =>
        match c, curr with
        | " ", EmptyString => split_str s' ""%string
        | " ", _           => rev_str curr::split_str s' ""%string
        | _  , _           => split_str s' (String c curr)
        end%char
    end.
  Definition match_pattern n pat :=
    let '(val, mask, e) := parse_pattern pat in
    if e then (N.land n mask =? val) else negb (N.land n mask =? val).
  Fixpoint match_all_patterns ns pats :=
    match ns, pats with
    | [n]   , [pat]      => match_pattern n pat
    | n::ns', pat::pats' => match_pattern n pat && match_all_patterns ns' pats'
    | _     , _          => false
    end.
  Fixpoint select_pattern_list {A} (ns : list N) (default : A) (cases : list (string * A)) : A :=
    match cases with
    | nil => default
    | (pats, act)::cases' =>
      let pats := split_str pats "" in
      if match_all_patterns ns pats then act
      else select_pattern_list ns default cases'
    end.
  Notation "pats => val" := (pats, val) (at level 100).
  Notation "'match[bits]' x , .. , y 'with' cases 'else' d 'end'" :=
    (let ns := (cons x .. (cons y nil) ..) in
     ltac:(let r := eval cbv [select_pattern_list match_pattern match_all_patterns parse_pattern shift_add split_str rev_str] in
                    (select_pattern_list ns d cases) in exact r))
    (at level 0).

  Notation "n .[ i , j ]" := (xbits n i j) (at level 30, format "n .[ i , j ]").
  Notation "n .[ b ]" := (xbits n b (b+1)) (at level 30, format "n .[ b ]").
End Notation.
Import Notation.

Variant inst :=
  | UDF .

Section Decoder.
  Variable n : N.

  Definition dp_imm := UDF.
  Definition B_cond :=
    let imm19 := n.[5,24] in
    let cond := n.[0,4] in
    UDF.
  Definition cond_branch :=
    let o1 := n.[24] in
    let imm19 := n.[5,24] in
    let o0 := n.[4] in
    let cond := n.[0,4] in
    match[bits] o1, o0 with
      [ "0  0" => B_cond
      ; "0  1" => UDF
      ; "1  -" => UDF
      ] else UDF end.
  Definition exc_gen :=
    let opc := n.[21,24] in
    let op2 := n.[2,5] in
    let LL := n.[0,2] in
    match[bits] opc, op2, LL with
      [ "-    001  - " => UDF (* Unallocated. *)
      ; "-    01x  - " => UDF (* Unallocated. *)
      ; "-    1xx  - " => UDF (* Unallocated. *)
      ; "000  000  00" => UDF (* Unallocated. *)
      ; "000  000  01" => UDF (* SVC *)
      ; "000  000  10" => UDF (* HVC *)
      ; "000  000  11" => UDF (* SMC *)
      ; "001  000  x1" => UDF (* Unallocated. *)
      ; "001  000  00" => UDF (* BRK *)
      ; "001  000  1x" => UDF (* Unallocated. *)
      ; "010  000  x1" => UDF (* Unallocated. *)
      ; "010  000  00" => UDF (* HLT *)
      ; "010  000  1x" => UDF (* Unallocated. *)
      ; "011  000  01" => UDF (* Unallocated. *)
      ; "011  000  1x" => UDF (* Unallocated. *)
      ; "100  000  - " => UDF (* Unallocated. *)
      ; "101  000  00" => UDF (* Unallocated. *)
      ; "101  000  01" => UDF (* DCPS1 *)
      ; "101  000  10" => UDF (* DCPS2 *)
      ; "101  000  11" => UDF (* DCPS3 *)
      ; "110  000  - " => UDF (* Unallocated. *)
      ; "111  000  - " => UDF (* Unallocated. *)
      ] else UDF end.
  Definition hints :=
    let CRm := n.[8,12] in
    let op2 := n.[5,8] in
    match[bits] CRm, op2 with
      [ "-     -  " => UDF (* HINT - *)
      ; "0000  000" => UDF (* NOP - *)
      ; "0000  001" => UDF (* YIELD - *)
      ; "0000  010" => UDF (* WFE - *)
      ; "0000  011" => UDF (* WFI - *)
      ; "0000  100" => UDF (* SEV - *)
      ; "0000  101" => UDF (* SEVL - *)
      ; "0000  110" => UDF (* DGH FEAT_DGH *)
      ; "0000  111" => UDF (* XPACD, XPACI, XPACLRI FEAT_PAuth *)
      ; "0001  000" => UDF (* PACIA, PACIA1716, PACIASP, PACIAZ, PACIZA - PACIA1716 variant FEAT_PAuth *)
      ; "0001  010" => UDF (* PACIB, PACIB1716, PACIBSP, PACIBZ, PACIZB - PACIB1716 variant FEAT_PAuth *)
      ; "0001  100" => UDF (* AUTIA, AUTIA1716, AUTIASP, AUTIAZ, AUTIZA - AUTIA1716 variant FEAT_PAuth *)
      ; "0001  110" => UDF (* AUTIB, AUTIB1716, AUTIBSP, AUTIBZ, AUTIZB - AUTIB1716 variant FEAT_PAuth *)
      ; "0010  000" => UDF (* ESB FEAT_RAS *)
      ; "0010  001" => UDF (* PSB CSYNC FEAT_SPE *)
      ; "0010  010" => UDF (* TSB CSYNC FEAT_TRF *)
      ; "0010  100" => UDF (* CSDB - *)
      ; "0011  000" => UDF (* PACIA, PACIA1716, PACIASP, PACIAZ, PACIZA - PACIAZ variant FEAT_PAuth *)
      ; "0011  001" => UDF (* PACIA, PACIA1716, PACIASP, PACIAZ, PACIZA - PACIASP variant FEAT_PAuth *)
      ; "0011  010" => UDF (* PACIB, PACIB1716, PACIBSP, PACIBZ, PACIZB - PACIBZ variant FEAT_PAuth *)
      ; "0011  011" => UDF (* PACIB, PACIB1716, PACIBSP, PACIBZ, PACIZB - PACIBSP variant FEAT_PAuth *)
      ; "0011  100" => UDF (* AUTIA, AUTIA1716, AUTIASP, AUTIAZ, AUTIZA - AUTIAZ variant FEAT_PAuth *)
      ; "0011  101" => UDF (* AUTIA, AUTIA1716, AUTIASP, AUTIAZ, AUTIZA - AUTIASP variant FEAT_PAuth *)
      ; "0011  110" => UDF (* AUTIB, AUTIB1716, AUTIBSP, AUTIBZ, AUTIZB - AUTIBZ variant FEAT_PAuth *)
      ; "0011  111" => UDF (* AUTIB, AUTIB1716, AUTIBSP, AUTIBZ, AUTIZB - AUTIBSP variant FEAT_PAuth *)
      ; "0100  xx0" => UDF (* BTI FEAT_BTI *)
      ] else UDF end.
  Definition barriers :=
    let CRm := n.[8,12] in
    let op2 := n.[5,8] in
    let Rt := n.[0,5] in
    match[bits] CRm, op2, Rt with
      [ "-       000  -      " => UDF (* Unallocated. *)
      ; "-       001  !=11111" => UDF (* Unallocated. *)
      ; "-       010  11111  " => UDF (* CLREX *)
      ; "-       101  11111  " => UDF (* DMB *)
      ; "-       110  11111  " => UDF (* ISB *)
      ; "-       111  !=11111" => UDF (* Unallocated. *)
      ; "-       111  11111  " => UDF (* SB *)
      ; "!=0x00  100  11111  " => UDF (* DSB *)
      ; "0000    100  11111  " => UDF (* SSBB *)
      ; "0001    011  -      " => UDF (* Unallocated. *)
      ; "001x    011  -      " => UDF (* Unallocated. *)
      ; "01xx    011  -      " => UDF (* Unallocated. *)
      ; "0100    100  11111  " => UDF (* PSSBB *)
      ; "1xxx    011  -      " => UDF (* Unallocated *)
      ] else UDF end.
  Definition pstate :=
    let op1 := n.[16,19] in
    let op2 := n.[5,8] in
    let Rt := n.[0,5] in
    match[bits] op1, op2, Rt with
      [ "-    -    !=11111" => UDF (* Unallocated. - *)
      ; "-    -    11111  " => UDF (* MSR (immediate) - *)
      ; "000  000  11111  " => UDF (* CFINV FEAT_FlagM *)
      ; "000  001  11111  " => UDF (* XAFLAG FEAT_FlagM2 *)
      ; "000  010  11111  " => UDF (* AXFLAG FEAT_FlagM2 *)
      ] else UDF end.
  Definition sys_inst :=
    let L := n.[21] in
    match[bits] L with
      [ "0" => UDF (* SYS *)
      ; "1" => UDF (* SYSL *)
      ] else UDF end.
  Definition sys_reg_move := UDF.
  Definition uncond_b_reg :=
    let opc := n.[21,25] in
    let op2 := n.[16,21] in
    let op3 := n.[10,16] in
    let Rn := n.[5,10] in
    let op4 := n.[0,5] in
    match[bits] opc, op2, op3, Rn, op4 with
      [ "-     !=11111  -         -        -      " => UDF (* Unallocated. - *)
      ; "0000  11111    000000    -        !=00000" => UDF (* Unallocated. - *)
      ; "0000  11111    000000    -        00000  " => UDF (* BR - *)
      ; "0000  11111    000001    -        -      " => UDF (* Unallocated. - *)
      ; "0000  11111    000010    -        !=11111" => UDF (* Unallocated. - *)
      ; "0000  11111    000010    -        11111  " => UDF (* BRAA, BRAAZ, BRAB, BRABZ - Key A, zero modifier variant FEAT_PAuth *)
      ; "0000  11111    000011    -        !=11111" => UDF (* Unallocated. - *)
      ; "0000  11111    000011    -        11111  " => UDF (* BRAA, BRAAZ, BRAB, BRABZ - Key B, zero modifier variant FEAT_PAuth *)
      ; "0000  11111    0001xx    -        -      " => UDF (* Unallocated. - *)
      ; "0000  11111    001xxx    -        -      " => UDF (* Unallocated. - *)
      ; "0000  11111    01xxxx    -        -      " => UDF (* Unallocated. - *)
      ; "0000  11111    1xxxxx    -        -      " => UDF (* Unallocated. - *)
      ; "0001  11111    000000    -        !=00000" => UDF (* Unallocated. - *)
      ; "0001  11111    000000    -        00000  " => UDF (* BLR - *)
      ; "0001  11111    000001    -        -      " => UDF (* Unallocated. - *)
      ; "0001  11111    000010    -        !=11111" => UDF (* Unallocated. - *)
      ; "0001  11111    000010    -        11111  " => UDF (* BLRAA, BLRAAZ, BLRAB, BLRABZ - Key A, zero modifier variant FEAT_PAuth *)
      ; "0001  11111    000011    -        !=11111" => UDF (* Unallocated. - *)
      ; "0001  11111    000011    -        11111  " => UDF (* BLRAA, BLRAAZ, BLRAB, BLRABZ - Key B, zero modifier variant FEAT_PAuth *)
      ; "0001  11111    0001xx    -        -      " => UDF (* Unallocated. - *)
      ; "0001  11111    001xxx    -        -      " => UDF (* Unallocated. - *)
      ; "0001  11111    01xxxx    -        -      " => UDF (* Unallocated. - *)
      ; "0001  11111    1xxxxx    -        -      " => UDF (* Unallocated. - *)
      ; "0010  11111    000000    -        !=00000" => UDF (* Unallocated. - *)
      ; "0010  11111    000000    -        00000  " => UDF (* RET - *)
      ; "0010  11111    000001    -        -      " => UDF (* Unallocated. - *)
      ; "0010  11111    000010    !=11111  !=11111" => UDF (* Unallocated. - *)
      ; "0010  11111    000010    11111    11111  " => UDF (* RETAA, RETAB - RETAA variant FEAT_PAuth *)
      ; "0010  11111    000011    !=11111  !=11111" => UDF (* Unallocated. - *)
      ; "0010  11111    000011    11111    11111  " => UDF (* RETAA, RETAB - RETAB variant FEAT_PAuth *)
      ; "0010  11111    0001xx    -        -      " => UDF (* Unallocated. - *)
      ; "0010  11111    001xxx    -        -      " => UDF (* Unallocated. - *)
      ; "0010  11111    01xxxx    -        -      " => UDF (* Unallocated. - *)
      ; "0010  11111    1xxxxx    -        -      " => UDF (* Unallocated. - *)
      ; "0011  11111    -         -        -      " => UDF (* Unallocated. - *)
      ; "0100  11111    000000    !=11111  !=00000" => UDF (* Unallocated. - *)
      ; "0100  11111    000000    !=11111  00000  " => UDF (* Unallocated. - *)
      ; "0100  11111    000000    11111    !=00000" => UDF (* Unallocated. - *)
      ; "0100  11111    000000    11111    00000  " => UDF (* ERET - *)
      ; "0100  11111    000001    -        -      " => UDF (* Unallocated. - *)
      ; "0100  11111    000010    !=11111  !=11111" => UDF (* Unallocated. - *)
      ; "0100  11111    000010    !=11111  11111  " => UDF (* Unallocated. - *)
      ; "0100  11111    000010    11111    !=11111" => UDF (* Unallocated. - *)
      ; "0100  11111    000010    11111    11111  " => UDF (* ERETAA, ERETAB - ERETAA variant FEAT_PAuth *)
      ; "0100  11111    000011    !=11111  !=11111" => UDF (* Unallocated. - *)
      ; "0100  11111    000011    !=11111  11111  " => UDF (* Unallocated. - *)
      ; "0100  11111    000011    11111    !=11111" => UDF (* Unallocated. - *)
      ; "0100  11111    000011    11111    11111  " => UDF (* ERETAA, ERETAB - ERETAB variant FEAT_PAuth *)
      ; "0100  11111    0001xx    -        -      " => UDF (* Unallocated. - *)
      ; "0100  11111    001xxx    -        -      " => UDF (* Unallocated. - *)
      ; "0100  11111    01xxxx    -        -      " => UDF (* Unallocated. - *)
      ; "0100  11111    1xxxxx    -        -      " => UDF (* Unallocated. - *)
      ; "0101  11111    !=000000  -        -      " => UDF (* Unallocated. - *)
      ; "0101  11111    000000    !=11111  !=00000" => UDF (* Unallocated. - *)
      ; "0101  11111    000000    !=11111  00000  " => UDF (* Unallocated. - *)
      ; "0101  11111    000000    11111    !=00000" => UDF (* Unallocated. - *)
      ; "0101  11111    000000    11111    00000  " => UDF (* DRPS - *)
      ; "011x  11111    -         -        -      " => UDF (* Unallocated. - *)
      ; "1000  11111    00000x    -        -      " => UDF (* Unallocated. - *)
      ; "1000  11111    000010    -        -      " => UDF (* BRAA, BRAAZ, BRAB, BRABZ - Key A, register modifier variant FEAT_PAuth *)
      ; "1000  11111    000011    -        -      " => UDF (* BRAA, BRAAZ, BRAB, BRABZ - Key B, register modifier variant FEAT_PAuth *)
      ; "1000  11111    0001xx    -        -      " => UDF (* Unallocated. - *)
      ; "1000  11111    001xxx    -        -      " => UDF (* Unallocated. - *)
      ; "1000  11111    01xxxx    -        -      " => UDF (* Unallocated. - *)
      ; "1000  11111    1xxxxx    -        -      " => UDF (* Unallocated. - *)
      ; "1001  11111    00000x    -        -      " => UDF (* Unallocated. - *)
      ; "1001  11111    000010    -        -      " => UDF (* BLRAA, BLRAAZ, BLRAB, BLRABZ - Key A, register modifier variant FEAT_PAuth *)
      ; "1001  11111    000011    -        -      " => UDF (* BLRAA, BLRAAZ, BLRAB, BLRABZ - Key B, register modifier variant FEAT_PAuth *)
      ; "1001  11111    0001xx    -        -      " => UDF (* Unallocated. - *)
      ; "1001  11111    001xxx    -        -      " => UDF (* Unallocated. - *)
      ; "1001  11111    01xxxx    -        -      " => UDF (* Unallocated. - *)
      ; "1001  11111    1xxxxx    -        -      " => UDF (* Unallocated. - *)
      ; "101x  11111    -         -        -      " => UDF (* Unallocated. - *)
      ; "11xx  11111    -         -        -      " => UDF (* Unallocated. - *)
      ] else UDF end.
  Definition uncond_b_imm :=
    let op := n.[31] in
    match[bits] op with
      [ "0" => UDF (* B *)
      ; "1" => UDF (* BL *)
      ] else UDF end.
  Definition comp_and_b :=
    let sf := n.[31] in
    let op := n.[24] in
    match[bits] sf, op with
      [ "0  0" => UDF (* CBZ - 32-bit variant *)
      ; "0  1" => UDF (* CBNZ - 32-bit variant *)
      ; "1  0" => UDF (* CBZ - 64-bit variant *)
      ; "1  1" => UDF (* CBNZ - 64-bit variant *)
      ] else UDF end.
  Definition test_and_b :=
    let op := n.[24] in
    match[bits] op with
      [ "0" => UDF (* TBZ *)
      ; "1" => UDF (* TBNZ *)
      ] else UDF end.
  Definition branch_exc :=
    let op0 := n.[29,32] in
    let op1 := n.[12,26] in
    let op2 := n.[0,5] in
    match[bits] op0, op1, op2 with
      [ "010  0xxxxxxxxxxxxx  -    " => cond_branch
      ; "110  00xxxxxxxxxxxx  -    " => exc_gen
      ; "110  01000000110010  11111" => hints
      ; "110  01000000110011  -    " => barriers
      ; "110  0100000xxx0100  -    " => pstate
      ; "110  0100x01xxxxxxx  -    " => sys_inst
      ; "110  0100x1xxxxxxxx  -    " => sys_reg_move
      ; "110  1xxxxxxxxxxxxx  -    " => uncond_b_reg
      ; "x00  -               -    " => uncond_b_imm
      ; "x01  0xxxxxxxxxxxxx  -    " => comp_and_b
      ; "x01  1xxxxxxxxxxxxx  -    " => test_and_b
      ] else UDF end.
  Definition load_store := UDF.
  Definition dp_reg := UDF.
  Definition dp_fp_simd := UDF.

  Definition decode :=
    let op0 := n.[25,29] in
    match[bits] op0 with
      [ "0000" => UDF
      ; "0001" => UDF
      ; "0010" => UDF
      ; "0011" => UDF
      ; "100x" => dp_imm
      ; "101x" => branch_exc
      ; "x1x0" => load_store
      ; "x101" => dp_reg
      ; "x111" => dp_fp_simd
      ] else UDF end.
End Decoder.
