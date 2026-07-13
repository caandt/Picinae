(*
   Armv8-A A64 lifter based on issue E.a
   https://developer.arm.com/documentation/ddi0487/ea/
 *)

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

(*DP imm*)
Variant arm_data_imm :=
  | ARM_ADD_IMM
  | ARM_ADDS_IMM
  | ARM_SUB_IMM
  | ARM_SUBS_IMM
  (*shifted*)
  | ARM_ADD_SHIFTED
  | ARM_ADDS_SHIFTED
  | ARM_SUB_SHIFTED
  | ARM_SUBS_SHIFTED
  (*extended*)
  | ARM_ADD_EXTENDED
  | ARM_ADDS_EXTENDED
  | ARM_SUB_EXTENDED
  | ARM_SUBS_EXTENDED
  (*compare*)
  | ARM_CMP_IMM
  | ARM_CMN_IMM
  (*logical imm*)
  | ARM_AND_IMM
  | ARM_ANDS_IMM
  | ARM_EOR_IMM
  | ARM_ORR_IMM
  | ARM_TST_IMM 
  (*move wide*)
  | ARM_MOVZ_IMM
  | ARM_MOVN_IMM
  | ARM_MOVK_IMM
  | ARM_MOV_IMM (*bitmask imm/wide imm/inverted wide imm*)
  (*PC relative addr*)
  | ARM_ADRP_IMM
  | ARM_ADR_IMM
  (*bitfield move*)
  | ARM_BFM_IMM
  | ARM_SBFM_IMM
  | ARM_UBFM_IMM
  (*bitfield insert extract*)
  | ARM_BFC_IMM
  | ARM_BFI_IMM
  | ARM_BFXIL_IMM
  | ARM_SBFIZ_IMM
  | ARM_SBFX_IMM
  | ARM_UBFX_IMM
  | ARM_UBFIZ_IMM
  (*extract*)
  | ARM_EXTR_IMM
  (*shift imm*)
  | ARM_ASR_IMM
  | ARM_LSL_IMM
  | ARM_LSR_IMM
  | ARM_ROR_IMM
  (*sign-extend zero-extend*)
  | ARM_SXTB_IMM
  | ARM_SXTH_IMM
  | ARM_SXTW_IMM
  | ARM_UXTB_IMM
  | ARM_UXTH_IMM
  (*conditional comparison*)
  | ARM_CCMN_IMM
  | ARM_CCMP_IMM.

(*DP reg*)
Variant arm_data_reg :=
  | ARM_ADD_REG
  | ARM_ADDS_REG
  | ARM_SUB_REG
  | ARM_SUBS_REG
  | ARM_CMN_REG
  | ARM_CMP_REG
  | ARM_NEG_REG
  | ARM_NEGS_REG
  (*arith extended*)
  | ARM_ADD_EXT_REG
  | ARM_ADDS_EXT_REG
  | ARM_SUB_EXT_REG
  | ARM_SUBS_EXT_REG
  | ARM_CMN_EXT_REG
  | ARM_CMP_EXT_REG
  (*w carry*)
  | ARM_ADC_REG
  | ARM_ADCS_REG
  | ARM_SBC_REG
  | ARM_SBCS_REG
  | ARM_NGC_REG
  | ARM_NGCS_REG
  (*logical - bitwise ops*)
  | ARM_AND_LOG_REG
  | ARM_ANDS_LOG_REG
  | ARM_BIC_LOG_REG
  | ARM_BICS_LOG_REG
  | ARM_EON_LOG_REG
  | ARM_EOR_LOG_REG
  | ARM_ORR_LOG_REG
  | ARM_MVN_LOG_REG
  | ARM_ORN_LOG_REG
  | ARM_TST_LOG_REG
  | ARM_MOV_LOG_REG (*mov register/mov register SP <-> reg*)
  (*shift register*)
  | ARM_ASRV_REG
  | ARM_LSLV_REG
  | ARM_LSRV_REG
  | ARM_RORV_REG
  (*conditional select*)
  | ARM_CSEL
  | ARM_CSINC  
  | ARM_CSINV  
  | ARM_CSNEG  
  | ARM_CSET  
  | ARM_CSETM  
  | ARM_CINC  
  | ARM_CINV  
  | ARM_CNEG
  (*conditional comparison*)
  | ARM_CCMN_REG  
  | ARM_CCMP_REG  
  | ARM_CSINC.  
Variant mul_div_reg :=
  | ARM_MADD
  | ARM_MSUB
  | ARM_MNEG
  | ARM_MUL
  | ARM_SMADDL
  | ARM_SMSUBL
  | ARM_SMNEGL
  | ARM_SMULL
  | ARM_SMULH
  | ARM_UMADDL
  | ARM_UMSUBL
  | ARM_UMNEGL
  | ARM_UMULL
  | ARM_UMULH
  | ARM_SDIV
  | ARM_UDIV.
Variant CRC32 :=
  | ARM_CRC32B
  | ARM_CRC32H
  | ARM_CRC32W
  | ARM_CRC32X
  | ARM_CRC32CB
  | ARM_CRC32CH
  | ARM_CRC32CW
  | ARM_CRC32CX.
Variant bit_ops :=
  | ARM_CLS
  | ARM_CLZ
  | ARM_RBIT
  | ARM_REV
  | ARM_REV16
  | ARM_REV32
  | ARM_REV64.

(*Branches*)
Variant inst :=
  (* decoding not implemented yet, treat as unpredictable *)
  | idk
  | ARM_UNPREDICTABLE
  | UDF (*ARM_UNDEFINED*)
  (*conditional branch (imm)*)
  | ARM_B_COND
  (*exception generation*)
  | ARM_SVC
  | ARM_HVC
  | ARM_SMC
  | ARM_BRK
  | ARM_HLT
  | ARM_DCPS1
  | ARM_DCPS2
  | ARM_DCPS3
  (*system*)
  | ARM_MSR
  | ARM_NOP
  | ARM_YIELD
  | ARM_WFE
  | ARM_WFI
  | ARM_SEV
  | ARM_SEVL
  | ARM_ESB
  | ARM_PSB_CSYNC
  | ARM_CLREX
  | ARM_DSB
  | ARM_DMB
  | ARM_ISB
  | ARM_SYS
  | ARM_MSR
  | ARM_SYSL
  | ARM_MRS
  (*unconditional branch(register)*)
  | ARM_BR
  | ARM_BLR
  | ARM_RET
  | ARM_ERET
  | ARM_DRPS
  (*unconditional branch(imm)*)
  | ARM_B
  | ARM_BL
  (*compare and branch(imm)*)
  | ARM_CBZ
  | ARM_CBNZ
  (*test and branch(imm)*)
  | ARM_TBZ
  | ARM_TBNZ

(*Loads and Stores*)
  (*exclusive/others*)
  | ARM_STXRB
  | ARM_STLXRB
  | ARM_LDXRB
  | ARM_LDXRH
  | ARM_LDAXRH
  | ARM_LDAXRB
  | ARM_STLLRB
  | ARM_STLLRH
  | ARM_STLRH
  | ARM_STLRB
  | ARM_STXRH
  | ARM_STLXRH
  | ARM_LDLARB
  | ARM_LDARB
  | ARM_LDARH
  | ARM_LDLARH
  | ARM_STXR
  | ARM_STLXR
  | ARM_STXP
  | ARM_LDXR
  | ARM_LDAXR
  | ARM_LDXP
  | ARM_LDAXP
  | ARM_STLLR
  | ARM_STLR
  | ARM_LDLAR
  | ARM_LDAR
  (*bunch of variants for these, refer to page C4-230*)
  | ARM_CASP
  | ARM_CASPA
  | ARM_CASPAL
  | ARM_CASPL
  | ARM_CASB
  | ARM_CASAB
  | ARM_CASALB
  | ARM_CASLB
  | ARM_CASH
  | ARM_CASAH
  | ARM_CASALH
  | ARM_CASLH
  | ARM_CAS
  | ARM_CASA
  | ARM_CASAL
  | ARM_CASL
  (*load register (literal)*)
  | ARM_LDR_LIT
  | ARM_LDRSW_LIT
  | ARM_PRFM_LIT
  (*load/store no-allocate pair (offset)*)
  | ARM_STNP
  | ARM_LDNP
  (*load/store register pair (post-indexed, pre-indexed, offset)*)
  | ARM_STP
  | ARM_LDP
  | ARM_LDPSW
  | ARM_STGP 
  (*load/store register (unscaled immediate)*)
  | ARM_STURB
  | ARM_LDURB
  | ARM_LDURSB
  | ARM_STURH
  | ARM_LDURH
  | ARM_LDURSH
  | ARM_STUR
  | ARM_LDUR
  | ARM_LDURSW
  | ARM_LDURSW
  | ARM_PFRM
  (*imm pre/post-indexed*)
  | ARM_STRB_IMM
  | ARM_LDRB_IMM
  | ARM_LDRSB_IMM
  | ARM_STR_IMM
  | ARM_LDR_IMM
  | ARM_STRH_IMM
  | ARM_LDRH_IMM
  | ARM_LDRSH_IMM
  | ARM_STR_IMM
  | ARM_LDR_IMM
  | ARM_LDRSW_IMM
  (*register unprivileged*)
  | ARM_STTRB
  | ARM_LDTRB
  | ARM_LDTRSB
  | ARM_STTRH
  | ARM_LDTRH
  | ARM_LDTRSH
  | ARM_STTR
  | ARM_LDTR
  | ARM_LDTRSW
  (*atomic memory ops*)
  | ARM_LDADDB
  | ARM_LDADDAB
  | ARM_LDADDALB
  | ARM_LDADDLB
  | ARM_STADDB
  | ARM_STADDLB
  | ARM_STCLRB
  | ARM_STCLRLB
  | ARM_STEORB
  | ARM_STEORLB
  | ARM_LDCLRB
  | ARM_LDCLRAB
  | ARM_LDCLRALB
  | ARM_LDCLRLB 
  | ARM_LDEORB
  | ARM_LDEORAB
  | ARM_LDEORALB
  | ARM_LDEORLB
  (*there's a lot more here, not sure how much to add. Pages C4-240-250*)
  (*load/store register*)
  | ARM_STRB_REG
  | ARM_LDRB_REG
  | ARM_LDRSB_REG
  | ARM_STR_REG
  | ARM_LDR_REG
  | ARM_STRH_REG
  | ARM_LDRH_REG
  | ARM_LDRSH_REG
  | ARM_STR_REG
  | ARM_LDR_REG
  | ARM_LDRSW_REG
  | ARM_PRFM_REG.
  (*TODO: There are way more load instructions than written out here, add to this section plz*)

Section Decoder.
  Variable n : N.

(** DP Immediate*)
  Definition pc_rel := 
    let op := n.[31] in
    match[bits] op with
    [ "0" => ARM_ADR (* ADR *)
    ; "1" => ARM_ADRP (* ADRP *)
    ] else UDF end.

  Definition add_sub_imm :=
    let sf := n.[31] in
    let op := n.[30] in
    let s_ := n.[29] in
    match[bits] sf, op, s_ with
  [ "0  0  0" => ARM_ADD_IMM (* ADD (immediate) - 32-bit variant on page C6-761 *)
  ; "0  0  1" => ARM_ADDS_IMM (* ADDS (immediate) - 32-bit variant on page C6-769 *)
  ; "0  1  0" => ARM_SUB_IMM (* SUB (immediate) - 32-bit variant on page C6-1311 *)
  ; "0  1  1" => ARM_SUBS_IMM (* SUBS (immediate) - 32-bit variant on page C6-1321 *)
  ; "1  0  0" => ARM_ADD_IMM (* ADD (immediate) - 64-bit variant on page C6-761 *)
  ; "1  0  1" => ARM_ADDS_IMM (* ADDS (immediate) - 64-bit variant on page C6-769 *)
  ; "1  1  0" => ARM_SUB_IMM (* SUB (immediate) - 64-bit variant on page C6-1311 *)
  ; "1  1  1" => ARM_SUBS_IMM (* SUBS (immediate) - 64-bit variant on page C6-1321 *)
  ] else UDF end.

  (*immediate, with tags*)
  Definition add_sub_imm_tags :=
    let sf := n.[31] in
    let op := n.[30] in
    let s_ := n.[29] in
    match[bits] sf, op, s_ with
  [ "0  -  -" => UDF (* Unallocated. - *)
  ; "1  -  1" => UDF (* Unallocated. - *)
  ; "1  0  0" => ARM_ADDG (* ADDG Armv8.5 *)
  ; "1  1  0" => ARM_SUBG (* SUBG Armv8.5 *)
  ] else UDF end.

  Definition move_wide_imm :=
    let sf := n.[31] in
    let opc := n.[29,31] in
    let hw := n.[21,23] in
    match[bits] sf, opc, hw with
  [ "-  01  - " => UDF (* Unallocated. *)
  ; "0  -   1x" => UDF (* Unallocated. *)
  ; "0  00  - " => ARM_MOVN (* MOVN - 32-bit variant on page C6-1100 *)
  ; "0  10  - " => ARM_MOVZ (* MOVZ - 32-bit variant on page C6-1102 *)
  ; "0  11  - " => ARM_MOVK (* MOVK - 32-bit variant on page C6-1098 *)
  ; "1  00  - " => ARM_MOVN (* MOVN - 64-bit variant on page C6-1100 *)
  ; "1  10  - " => ARM_MOVZ (* MOVZ - 64-bit variant on page C6-1102 *)
  ; "1  11  - " => ARM_MOVK (* MOVK - 64-bit variant on page C6-1098 *)
  ] else UDF end.

  Definition bitfield :=
    let sf := n.[31] in
    let opc := n.[29,31] in
    let n_ := n.[22] in
    match[bits] sf, opc, n_ with
  [ "-  11  -" => UDF (* Unallocated. *)
  ; "0  -   1" => UDF (* Unallocated. *)
  ; "0  00  0" => ARM_SBFM (* SBFM - 32-bit variant on page C6-1170 *)
  ; "0  01  0" => ARM_BFM (* BFM - 32-bit variant on page C6-804 *)
  ; "0  10  0" => ARM_UBFM (* UBFM - 32-bit variant on page C6-1351 *)
  ; "1  -   0" => UDF (* Unallocated. *)
  ; "1  00  1" => ARM_SBFM (* SBFM - 64-bit variant on page C6-1170 *)
  ; "1  01  1" => ARM_BFM (* BFM - 64-bit variant on page C6-804 *)
  ; "1  10  1" => ARM_UBFM (* UBFM - 64-bit variant on page C6-1351 *)
  ] else UDF end.

  Definition extract :=
    let sf := n.[31] in
    let op21 := n.[29,31] in
    let n_ := n.[22] in
    let o0 := n.[21] in
    let imms := n.[10,16] in
    match[bits] sf, op, s_, opcode2 with
  [ "-  x1  -  -" => ARM_- (* - Unallocated. *)
  ; "-  00  -  1" => ARM_- (* - Unallocated. *)
  ; "-  1x  -  -" => ARM_- (* - Unallocated. *)
  ; "0  -   -  -" => ARM_1xxxxx (* 1xxxxx Unallocated. *)
  ; "0  -   1  -" => ARM_- (* - Unallocated. *)
  ; "0  00  0  0" => ARM_0xxxxx (* 0xxxxx EXTR - 32-bit variant on page C6-903 *)
  ; "1  -   0  -" => ARM_- (* - Unallocated. *)
  ; "1  00  1  0" => ARM_- (* - EXTR - 64-bit variant on page C6-903 *)
  ] else UDF end.

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
      [ "0  0" => B_cond (* B.cond *)
      ; "0  1" => UDF (* Unallocated. *)
      ; "1  -" => UDF (* Unallocated. *)
      ] else UDF end.

  Definition exc_gen :=
    let opc := n.[21,24] in
    let op2 := n.[2,5] in
    let LL := n.[0,2] in
    match[bits] opc, op2, LL with
      [ "-    xx1  - " => UDF (* Unallocated. *)
      ; "-    x1x  - " => UDF (* Unallocated. *)
      ; "-    1xx  - " => UDF (* Unallocated. *)
      ; "000  000  00" => UDF (* Unallocated. *)
      ; "000  000  01" => ARM_SVC (* SVC *)
      ; "000  000  10" => ARM_HVC (* HVC *)
      ; "000  000  11" => ARM_SMC (* SMC *)
      ; "001  000  x1" => UDF (* Unallocated. *)
      ; "001  000  00" => ARM_BRK (* BRK *)
      ; "001  000  1x" => UDF (* Unallocated. *)
      ; "010  000  x1" => UDF (* Unallocated. *)
      ; "010  000  00" => ARM_HLT (* HLT *)
      ; "010  000  1x" => UDF (* Unallocated. *)
      ; "011  000  01" => UDF (* Unallocated. *)
      ; "011  000  1x" => UDF (* Unallocated. *)
      ; "100  000  00" => UDF (* Unallocated. *)
      ; "101  000  00" => UDF (* Unallocated. *)
      ; "101  000  01" => ARM_DCPS1 (* DCPS1 *)
      ; "101  000  10" => ARM_DCPS2 (* DCPS2 *)
      ; "101  000  11" => ARM_DCPS3 (* DCPS3 *)
      ; "110  000  - " => UDF (* Unallocated. *)
      ; "111  000  01" => UDF (* Unallocated. *)
      ; "111  000  1x" => UDF (* Unallocated. *)
      ] else UDF end.

  Definition hints :=
    let CRm := n.[8,12] in
    let op2 := n.[5,8] in
match[bits] CRm, op2 with
  [ "-     -  " => ARM_HINT (* HINT - *)
  ; "0000  000" => ARM_NOP (* NOP - *)
  ; "0000  001" => ARM_YIELD (* YIELD - *)
  ; "0000  010" => ARM_WFE (* WFE - *)
  ; "0000  011" => ARM_WFI (* WFI - *)
  ; "0000  100" => ARM_SEV (* SEV - *)
  ; "0000  101" => ARM_SEVL (* SEVL - *)
  ; "0000  111" => ARM_XPACD (* XPACD, XPACI, XPACLRI Armv8.3 *)
  ; "0001  000" => ARM_PACIA (* PACIA, PACIA1716, PACIASP, PACIAZ, PACIZA - PACIA1716 variant on page C6-1133 Armv8.3 *)
  ; "0001  010" => ARM_PACIB (* PACIB, PACIB1716, PACIBSP, PACIBZ, PACIZB - PACIB1716 variant on page C6-1135 Armv8.3 *)
  ; "0001  100" => ARM_AUTIA (* AUTIA, AUTIA1716, AUTIASP, AUTIAZ, AUTIZA - AUTIA1716 variant on page C6-794 Armv8.3 *)
  ; "0001  110" => ARM_AUTIB (* AUTIB, AUTIB1716, AUTIBSP, AUTIBZ, AUTIZB - AUTIB1716 variant on page C6-796 Armv8.3 *)
  ; "0010  000" => ARM_ESB (* ESB Armv8.2 *)
  ; "0010  001" => ARM_PSB_CSYNC (* PSB_CSYNC Armv8.2 *)
  ; "0010  010" => ARM_TSB_CSYNC (* TSB_CSYNC Armv8.4 *)
  ; "0010  100" => ARM_CSDB (* CSDB - *)
  ; "0011  000" => ARM_PACIA (* PACIA, PACIA1716, PACIASP, PACIAZ, PACIZA - PACIAZ variant on page C6-1133 Armv8.3 *)
  ; "0011  001" => ARM_PACIA (* PACIA, PACIA1716, PACIASP, PACIAZ, PACIZA - PACIASP variant on page C6-1133 Armv8.3 *)
  ; "0011  010" => ARM_PACIB (* PACIB, PACIB1716, PACIBSP, PACIBZ, PACIZB - PACIBZ variant on page C6-1135 Armv8.3 *)
  ; "0011  011" => ARM_PACIB (* PACIB, PACIB1716, PACIBSP, PACIBZ, PACIZB - PACIBSP variant on page C6-1135 Armv8.3 *)
  ; "0011  100" => ARM_AUTIA (* AUTIA, AUTIA1716, AUTIASP, AUTIAZ, AUTIZA - AUTIAZ variant on page C6-794 Armv8.3 *)
  ; "0011  101" => ARM_AUTIA (* AUTIA, AUTIA1716, AUTIASP, AUTIAZ, AUTIZA - AUTIASP variant on page C6-794 Armv8.3 *)
  ; "0011  110" => ARM_AUTIB (* AUTIB, AUTIB1716, AUTIBSP, AUTIBZ, AUTIZB - AUTIBZ variant on page C6-796 Armv8.3 *)
  ; "0011  111" => ARM_AUTIB (* AUTIB, AUTIB1716, AUTIBSP, AUTIBZ, AUTIZB - AUTIBSP variant on page C6-796 Armv8.3 *)
  ; "0100  xx0" => ARM_BTI (* BTI Armv8.5 *)
  ] else UDF end.

  Definition barriers :=
    let CRm := n.[8,12] in
    let op2 := n.[5,8] in
    let Rt := n.[0,5] in
    match[bits] CRm, op2, rt with
    [ "-       000  -      " => UDF (* Unallocated. *)
    ; "-       001  -      " => UDF (* Unallocated. *)
    ; "-       010  11111  " => ARM_CLREX (* CLREX *)
    ; "-       101  11111  " => ARM_DMB (* DMB *)
    ; "-       110  11111  " => ARM_ISB (* ISB *)
    ; "-       111  !=11111" => UDF (* Unallocated. *)
    ; "-       111  11111  " => ARM_SB (* SB *)
    ; "!=0x00  100  11111  " => ARM_DSB (* DSB *)
    ; "0000    100  11111  " => ARM_SSBB (* SSBB *)
    ; "0001    011  -      " => UDF (* Unallocated. *)
    ; "001x    011  -      " => UDF (* Unallocated. *)
    ; "01xx    011  -      " => UDF (* Unallocated. *)
    ; "0100    100  11111  " => ARM_PSSBB (* PSSBB *)
    ; "1xxx    011  -      " => UDF (* Unallocated. *)
    ] else UDF end.

  Definition pstate :=
    let op1 := n.[16,19] in
    let op2 := n.[5,8] in
    let Rt := n.[0,5] in
    match[bits] op1, op2, rt with
      [ "-    -    !=11111" => UDF (* Unallocated. - *)
      ; "-    -    11111  " => ARM_MSR_IMM (* MSR (immediate) - *)
      ; "000  000  11111  " => ARM_CFINV (* CFINV Armv8.4 *)
      ; "000  001  11111  " => ARM_XAFLAG (* XAFLAG Armv8.5 *)
      ; "000  010  11111  " => ARM_AXFLAG (* AXFLAG Armv8.5 *)
      ] else UDF end.
      
  Definition sys_inst :=
    let L := n.[21] in
    match[bits] L with
      [ "0" => ARM_SYS (* SYS *)
      ; "1" => ARM_SYSL (* SYSL *)
      ] else UDF end.

  Definition sys_reg_move :=
    let L := n.[21] in
    match[bits] L with
      [ "0" => ARM_MSR_REG (* MSR (register) *)
      ; "1" => ARM_MRS (* MRS *)
      ] else UDF end.

  Definition uncond_b_reg :=
    let opc := n.[21,25] in
    let op2 := n.[16,21] in
    let op3 := n.[10,16] in
    let Rn := n.[5,10] in
    let op4 := n.[0,5] in
  match[bits] opc, op2, op3, rn, op4 with
    [ "-     !=11111   -         -        -      " => UDF (* Unallocated. - *)
    ; "0000  11111     000000    -        !=00000" => UDF (* Unallocated. - *)
    ; "0000  11111     000000    -        00000  " => ARM_BR (* BR - *)
    ; "0000  11111     000001    -        -      " => UDF (* Unallocated. - *)
    ; "0000  11111     000010    -        !=11111" => UDF (* Unallocated. - *)
    ; "0000  11111     000010    -        11111  " => ARM_BRAA (* BRAA, BRAAZ, BRAB, BRABZ - Key A, zero modifier variant on page C6-817 Armv8.3 *)
    ; "0000  11111     000011    -        !=11111" => UDF (* Unallocated. - *)
    ; "0000  11111     000011    -        11111  " => ARM_BRAA (* BRAA, BRAAZ, BRAB, BRABZ - Key B, zero modifier variant on page C6-817 Armv8.3 *)
    ; "0000  11111     0001xx    -        -      " => UDF (* Unallocated. - *)
    ; "0000  11111     001xxx    -        -      " => UDF (* Unallocated. - *)
    ; "0000  11111     01xxxx    -        -      " => UDF (* Unallocated. - *)
    ; "0000  11111     1xxxxx    -        -      " => UDF (* Unallocated. - *)
    ; "0001  11111     000000    -        !=00000" => UDF (* Unallocated. - *)
    ; "0001  11111     000000    -        00000  " => ARM_BLR (* BLR - *)
    ; "0001  11111     000001    -        -      " => UDF (* Unallocated. - *)
    ; "0001  11111     000010    -        !=11111" => UDF (* Unallocated. - *)
    ; "0001  11111     000010    -        11111  " => ARM_BLRAA (* BLRAA, BLRAAZ, BLRAB, BLRABZ - Key A, *)
    ; "zero  modifier  variant   on       page   " => ARM_C6-814 (* C6-814 Armv8.3 *)
    ; "0001  11111     000011    -        !=11111" => UDF (* Unallocated. - *)
    ; "0001  11111     000011    -        11111  " => ARM_BLRAA (* BLRAA, BLRAAZ, BLRAB, BLRABZ - Key B, *)
    ; "zero  modifier  variant   on       page   " => ARM_C6-814 (* C6-814 Armv8.3 *)
    ; "0001  11111     0001xx    -        -      " => UDF (* Unallocated. - *)
    ; "0001  11111     001xxx    -        -      " => UDF (* Unallocated. - *)
    ; "0001  11111     01xxxx    -        -      " => UDF (* Unallocated. - *)
    ; "0001  11111     1xxxxx    -        -      " => UDF (* Unallocated. - *)
    ; "0010  11111     000000    -        !=00000" => UDF (* Unallocated. - *)
    ; "0010  11111     000000    -        00000  " => ARM_RET (* RET - *)
    ; "0010  11111     000001    -        -      " => UDF (* Unallocated. - *)
    ; "0010  11111     000010    !=11111  !=11111" => UDF (* Unallocated. - *)
    ; "0010  11111     000010    11111    11111  " => ARM_RETAA (* RETAA, RETAB - RETAA variant on page C6-1148 Armv8.3 *)
    ; "0010  11111     000011    !=11111  !=11111" => UDF (* Unallocated. - *)
    ; "0010  11111     000011    11111    11111  " => ARM_RETAA (* RETAA, RETAB - RETAB variant on page C6-1148 Armv8.3 *)
    ; "0010  11111     0001xx    -        -      " => UDF (* Unallocated. - *)
    ; "0010  11111     001xxx    -        -      " => UDF (* Unallocated. - *)
    ; "0010  11111     01xxxx    -        -      " => UDF (* Unallocated. - *)
    ; "0010  11111     1xxxxx    -        -      " => UDF (* Unallocated. - *)
    ; "0011  11111     -         -        -      " => UDF (* Unallocated. - *)
    ; "0100  11111     000000    !=11111  !=00000" => UDF (* Unallocated. - *)
    ; "0100  11111     000000    !=11111  00000  " => UDF (* Unallocated. - *)
    ; "0100  11111     000000    11111    !=00000" => UDF (* Unallocated. - *)
    ; "0100  11111     000000    11111    00000  " => ARM_ERET (* ERET - *)
    ; "0100  11111     000001    -        -      " => UDF (* Unallocated. - *)
    ; "0100  11111     000010    !=11111  !=11111" => UDF (* Unallocated. - *)
    ; "0100  11111     000010    !=11111  11111  " => UDF (* Unallocated. - *)
    ; "0100  11111     000010    11111    !=11111" => UDF (* Unallocated. - *)
    ; "0100  11111     000010    11111    11111  " => ARM_ERETAA (* ERETAA, ERETAB - ERETAA variant on page C6-901 Armv8.3 *)
    ; "0100  11111     000011    !=11111  !=11111" => UDF (* Unallocated. - *)
    ; "0100  11111     000011    !=11111  11111  " => UDF (* Unallocated. - *)
    ; "0100  11111     000011    11111    !=11111" => UDF (* Unallocated. - *)
    ; "0100  11111     000011    11111    11111  " => ARM_ERETAA (* ERETAA, ERETAB - ERETAB variant on page C6-901 Armv8.3 *)
    ; "0100  11111     0001xx    -        -      " => UDF (* Unallocated. - *)
    ; "0100  11111     001xxx    -        -      " => UDF (* Unallocated. - *)
    ; "0100  11111     01xxxx    -        -      " => UDF (* Unallocated. - *)
    ; "0100  11111     1xxxxx    -        -      " => UDF (* Unallocated. - *)
    ; "0101  11111     !=000000  -        -      " => UDF (* Unallocated. - *)
    ; "0101  11111     000000    !=11111  !=00000" => UDF (* Unallocated. - *)
    ; "0101  11111     000000    !=11111  00000  " => UDF (* Unallocated. - *)
    ; "0101  11111     000000    11111    !=00000" => UDF (* Unallocated. - *)
    ; "0101  11111     000000    11111    00000  " => ARM_DRPS (* DRPS - *)
    ; "011x  11111     -         -        -      " => UDF (* Unallocated. - *)
    ; "1000  11111     00000x    -        -      " => UDF (* Unallocated. - *)
    ; "1000  11111     000010    -        -      " => ARM_BRAA_REG (* BRAA, BRAAZ, BRAB, BRABZ - Key A, register modifier variant on page C6-817 Armv8.3 *)
    ; "1000  11111     000011    -        -      " => ARM_BRAA_REG (* BRAA, BRAAZ, BRAB, BRABZ - Key B, register modifier variant on page C6-817 Armv8.3 *)
    ; "1000  11111     0001xx    -        -      " => UDF (* Unallocated. - *)
    ; "1000  11111     001xxx    -        -      " => UDF (* Unallocated. - *)
    ; "1000  11111     01xxxx    -        -      " => UDF (* Unallocated. - *)
    ; "1000  11111     1xxxxx    -        -      " => UDF (* Unallocated. - *)
    ; "1001  11111     00000x    -        -      " => UDF (* Unallocated. - *)
    ; "1001  11111     000010    -        -      " => ARM_BLRAA_REG (* BLRAA, BLRAAZ, BLRAB, BLRABZ - Key A, register modifier variant on page C6-814 Armv8.3 *)
    ; "1001  11111     000011    -        -      " => ARM_BLRAA_REG (* BLRAA, BLRAAZ, BLRAB, BLRABZ - Key B, register modifier variant on page C6-814 Armv8.3 *)
    ; "1001  11111     0001xx    -        -      " => UDF (* Unallocated. - *)
    ; "1001  11111     001xxx    -        -      " => UDF (* Unallocated. - *)
    ; "1001  11111     01xxxx    -        -      " => UDF (* Unallocated. - *)
    ; "1001  11111     1xxxxx    -        -      " => UDF (* Unallocated. - *)
    ; "101x  11111     -         -        -      " => UDF (* Unallocated. - *)
    ; "11xx  11111     -         -        -      " => UDF (* Unallocated. - *)
    ] else UDF end.

  Definition uncond_b_imm :=
    let op := n.[31] in
    match[bits] op with
      [ "0" => ARM_B (* B *)
      ; "1" => ARM_BL (* BL *)
      ] else UDF end.

  Definition comp_and_b :=
    let sf := n.[31] in
    let op := n.[24] in
    match[bits] sf, op with
      [ "0  0" => ARM_CBZ (* CBZ - 32-bit variant *)
      ; "0  1" => ARM_CBNZ (* CBNZ - 32-bit variant *)
      ; "1  0" => ARM_CBZ (* CBZ - 64-bit variant *)
      ; "1  1" => ARM_CBNZ (* CBNZ - 64-bit variant *)
      ] else UDF end.

  Definition test_and_b :=
    let op := n.[24] in
    match[bits] op with
      [ "0" => ARM_TBZ (* TBZ *)
      ; "1" => ARM_TBNZ (* TBNZ *)
      ] else UDF end.

  Definition branch_exc :=
    let op0 := n.[29,32] in
    let op1 := n.[12,26] in
    let op2 := n.[0,5] in
    match[bits] op0, op1, op2 with
      [ "010  0xxxxxxxxxxxxx  -    " => cond_branch (* Conditional branch (immediate) *)
      ; "110  00xxxxxxxxxxxx  -    " => exc_gen (* Exception generation on page C4-258 *)
      ; "110  01000000110010  11111" => hints (* Hints on page C4-258 *)
      ; "110  01000000110011  -    " => barriers (* Barriers on page C4-260 *)
      ; "110  0100000xxx0100  -    " => pstate (* PSTATE on page C4-260 *)
      ; "110  0100x01xxxxxxx  -    " => sys_inst (* System instructions on page C4-261 *)
      ; "110  0100x1xxxxxxxx  -    " => sys_reg_move (* System register move on page C4-261 *)
      ; "110  1xxxxxxxxxxxxx  -    " => uncond_b_reg (* Unconditional branch (register) on page C4-262 *)
      ; "x00  -               -    " => uncond_b_imm (* Unconditional branch (immediate) on page C4-264 *)
      ; "x01  0xxxxxxxxxxxxx  -    " => comp_and_b (* Compare and branch (immediate) on page C4-265 *)
      ; "x01  1xxxxxxxxxxxxx  -    " => test_and_b (* Test and branch (immediate) on page C4-265 *)
      ] else UDF end.

  Definition load_store_mem_tags :=
    let opc := n.[22,24] in
    let imm9 := n.[12,21] in
    let op2 := n.[10,12] in
    match[bits] opc, imm9, op2 with
  [ "00  -            01" => ARM_STG_POST (* STG - Post-index variant on page C6-1207 Armv8.5 *)
  ; "00  -            10" => ARM_STG_SIGN (* STG - Signed offset variant on page C6-1207 Armv8.5 *)
  ; "00  -            11" => ARM_STG_PRE (* STG - Pre-index variant on page C6-1207 Armv8.5 *)
  ; "00  000000000    00" => ARM_STZGM (* STZGM Armv8.5 *)
  ; "01  -            00" => ARM_LDG (* LDG Armv8.5 *)
  ; "01  -            01" => ARM_STZG_POST (* STZG - Post-index variant on page C6-1305 Armv8.5 *)
  ; "01  -            10" => ARM_STZG_SIGN (* STZG - Signed offset variant on page C6-1305 Armv8.5 *)
  ; "01  -            11" => ARM_STZG_PRE (* STZG - Pre-index variant on page C6-1305 Armv8.5 *)
  ; "10  -            01" => ARM_ST2G_POST (* ST2G - Post-index variant on page C6-1187 Armv8.5 *)
  ; "10  -            10" => ARM_ST2G_SIGN (* ST2G - Signed offset variant on page C6-1187 Armv8.5 *)
  ; "10  -            11" => ARM_ST2G_PRE (* ST2G - Pre-index variant on page C6-1187 Armv8.5 *)
  ; "10  !=000000000  00" => UDF (* Unallocated. - *)
  ; "10  000000000    00" => ARM_STGM (* STGM Armv8.5 *)
  ; "11  -            01" => ARM_STZ2G_POST (* STZ2G - Post-index variant on page C6-1303 Armv8.5 *)
  ; "11  -            10" => ARM_STZ2G_SIGN (* STZ2G - Signed offset variant on page C6-1303 Armv8.5 *)
  ; "11  -            11" => ARM_STZ2G_PRE (* STZ2G - Pre-index variant on page C6-1303 Armv8.5 *)
  ; "11  !=000000000  00" => UDF (* Unallocated. - *)
  ; "11  000000000    00" => ARM_LDGM (* LDGM Armv8.5 *)
  ] else UDF end.


  Definition load_store_exclusive :=
    let size := n.[30,32] in
    let o2 := n.[23] in
    let l_ := n.[22] in
    let o1 := n.[21] in
    let o0 := n.[15] in
    let rt2 := n.[10,15] in
    match[bits] sf, o2, l_, o1, o0, rt2 with
  [ "-   1  -  1  -  !=11111" => UDF (* Unallocated. - *)
  ; "0x  0  -  1  -  !=11111" => UDF (* Unallocated. - *)
  ; "00  0  0  0  0  -      " => ARM_STXRB (* STXRB - *)
  ; "00  0  0  0  1  -      " => ARM_STLXRB (* STLXRB - *)
  ; "00  0  0  1  0  11111  " => ARM_CASP (* CASP, CASPA, CASPAL, CASPL - 32-bit, no memory ordering variant on page C6-568 ARMv8.1 *)
  ; "00  0  0  1  1  11111  " => ARM_CASP (* CASP, CASPA, CASPAL, CASPL - 32-bit, release variant on page C6-568 ARMv8.1 *)
  ; "00  0  1  0  0  -      " => ARM_LDXRB (* LDXRB - *)
  ; "00  0  1  0  1  -      " => ARM_LDAXRB (* LDAXRB - *)
  ; "00  0  1  1  0  11111  " => ARM_CASP (* CASP, CASPA, CASPAL, CASPL - 32-bit, acquire variant on page C6-568 ARMv8.1 *)
  ; "00  0  1  1  1  11111  " => ARM_CASP (* CASP, CASPA, CASPAL, CASPL - 32-bit, acquire and release variant on page C6-568 ARMv8.1 *)
  ; "00  1  0  0  0  -      " => ARM_STLLRB (* STLLRB ARMv8.1 *)
  ; "00  1  0  0  1  -      " => ARM_STLRB (* STLRB - *)
  ; "00  1  0  1  0  11111  " => ARM_CASB (* CASB, CASAB, CASALB, CASLB - No memory ordering variant on page C6-564 ARMv8.1 *)
  ; "00  1  0  1  1  11111  " => ARM_CASB (* CASB, CASAB, CASALB, CASLB - Release variant on page C6-564 ARMv8.1 *)
  ; "00  1  1  0  0  -      " => ARM_LDLARB (* LDLARB ARMv8.1 *)
  ; "00  1  1  0  1  -      " => ARM_LDARB (* LDARB - *)
  ; "00  1  1  1  0  11111  " => ARM_CASB (* CASB, CASAB, CASALB, CASLB - Acquire variant on page C6-564 ARMv8.1 *)
  ; "00  1  1  1  1  11111  " => ARM_CASB (* CASB, CASAB, CASALB, CASLB - Acquire and release variant on page C6-564 ARMv8.1 *)
  ; "01  0  0  0  0  -      " => ARM_STXRH (* STXRH - *)
  ; "01  0  0  0  1  -      " => ARM_STLXRH (* STLXRH - *)
  ; "01  0  0  1  0  11111  " => ARM_CASP (* CASP, CASPA, CASPAL, CASPL - 64-bit, no memory ordering variant on page C6-569 ARM *)
  ; "01  0  0  1  1  11111  " => ARM_CASP (* CASP, CASPA, CASPAL, CASPL - 64-bit, release variant on page C6-569 ARMv8.1 *)
  ; "01  0  1  0  0  -      " => ARM_LDXRH (* LDXRH - *)
  ; "01  0  1  0  1  -      " => ARM_LDAXRH (* LDAXRH - *)
  ; "01  0  1  1  0  11111  " => ARM_CASP (* CASP, CASPA, CASPAL, CASPL - 64-bit, acquire variant on *)
  ; "01  0  1  1  1  11111  " => ARM_CASP (* CASP, CASPA, CASPAL, CASPL - 64-bit, acquire and *)
  ; "01  1  0  0  0  -      " => ARM_STLLRH (* STLLRH ARMv8.1 *)
  ; "01  1  0  0  1  -      " => ARM_STLRH (* STLRH - *)
  ; "01  1  0  1  0  11111  " => ARM_CASH (* CASH, CASAH, CASALH, CASLH - No memory ordering *)
  ; "01  1  0  1  1  11111  " => ARM_CASH (* CASH, CASAH, CASALH, CASLH - Release variant on *)
  ; "01  1  1  0  0  -      " => ARM_LDLARH (* LDLARH ARMv8.1 *)
  ; "01  1  1  0  1  -      " => ARM_LDARH (* LDARH - *)
  ; "01  1  1  1  0  11111  " => ARM_CASH (* CASH, CASAH, CASALH, CASLH - Acquire variant on *)
  ; "01  1  1  1  1  11111  " => ARM_CASH (* CASH, CASAH, CASALH, CASLH - Acquire and release *)
  ; "10  0  0  0  0  -      " => ARM_STXR (* STXR - 32-bit variant on page C6-922 - *)
  ; "10  0  0  0  1  -      " => ARM_STLXR (* STLXR - 32-bit variant on page C6-859 - *)
  ; "10  0  0  1  0  -      " => ARM_STXP (* STXP - 32-bit variant on page C6-920 - *)
  ; "10  0  0  1  1  -      " => ARM_STLXP (* STLXP - 32-bit variant on page C6-856 - *)
  ; "10  0  1  0  0  -      " => ARM_LDXR (* LDXR - 32-bit variant on page C6-750 - *)
  ; "10  0  1  0  1  -      " => ARM_LDAXR (* LDAXR - 32-bit variant on page C6-643 - *)
  ; "10  0  1  1  0  -      " => ARM_LDXP (* LDXP - 32-bit variant on page C6-748 - *)
  ; "10  0  1  1  1  -      " => ARM_LDAXP (* LDAXP - 32-bit variant on page C6-641 - *)
  ; "10  1  0  0  0  -      " => ARM_STLLR (* STLLR - 32-bit variant on page C6-852 ARMv8.1 *)
  ; "10  1  0  0  1  -      " => ARM_STLR (* STLR - 32-bit variant on page C6-853 - *)
  ; "10  1  0  1  0  11111  " => ARM_CAS (* CAS, CASA, CASAL, CASL - 32-bit, no memory ordering *)
  ; "10  1  0  1  1  11111  " => ARM_CAS (* CAS, CASA, CASAL, CASL - 32-bit, release variant on *)
  ; "10  1  1  0  0  -      " => ARM_LDLAR (* LDLAR - 32-bit variant on page C6-661 *)
  ; "10  1  1  0  1  -      " => ARM_LDAR (* LDAR - 32-bit variant on page C6-638 - *)
  ; "10  1  1  1  0  11111  " => ARM_CAS (* CAS, CASA, CASAL, CASL - 32-bit, acquire variant on *)
  ; "10  1  1  1  1  11111  " => ARM_CAS (* CAS, CASA, CASAL, CASL - 32-bit, acquire and release *)
  ; "11  0  0  0  0  -      " => ARM_STXR (* STXR - 64-bit variant on page C6-922 - *)
  ; "11  0  0  0  1  -      " => ARM_STLXR (* STLXR - 64-bit variant on page C6-859 - *)
  ; "11  0  0  1  0  -      " => ARM_STXP (* STXP - 64-bit variant on page C6-920 - *)
  ; "11  0  0  1  1  -      " => ARM_STLXP (* STLXP - 64-bit variant on page C6-856 - *)
  ; "11  0  1  0  0  -      " => ARM_LDXR (* LDXR - 64-bit variant on page C6-750 - *)
  ; "11  0  1  0  1  -      " => ARM_LDAXR (* LDAXR - 64-bit variant on page C6-643 - *)
  ; "11  0  1  1  0  -      " => ARM_LDXP (* LDXP - 64-bit variant on page C6-748 - *)
  ; "11  0  1  1  1  -      " => ARM_LDAXP (* LDAXP - 64-bit variant on page C6-641 - *)
  ; "11  1  0  0  0  -      " => ARM_STLLR (* STLLR - 64-bit variant on page C6-852 ARMv8.1 *)
  ; "11  1  0  0  1  -      " => ARM_STLR (* STLR - 64-bit variant on page C6-853 - *)
  ; "11  1  0  1  0  11111  " => ARM_CAS (* CAS, CASA, CASAL, CASL - 64-bit, no memory ordering *)
  ; "11  1  0  1  1  11111  " => ARM_CAS (* CAS, CASA, CASAL, CASL - 64-bit, release variant on *)
  ; "11  1  1  0  0  -      " => ARM_LDLAR (* LDLAR - 64-bit variant on page C6-661 ARMv8.1 *)
  ; "11  1  1  0  1  -      " => ARM_LDAR (* LDAR - 64-bit variant on page C6-638 - *)
  ; "11  1  1  1  0  11111  " => ARM_CAS (* CAS, CASA, CASAL, CASL - 64-bit, acquire variant on *)
  ; "11  1  1  1  1  11111  " => ARM_CAS (* CAS, CASA, CASAL, CASL - 64-bit, acquire and release *)
  ] else UDF end.

  Definition ld_str_unscaled_immediate :=
    let size := n.[30,32] in 
    let opc := n.[22,24] in
    match[bits] size, opc with
  [ "00  00" => ARM_STLURB (* STLURB Armv8.4 *)
  ; "00  01" => ARM_LDAPURB (* LDAPURB Armv8.4 *)
  ; "00  10" => ARM_LDAPURSB (* LDAPURSB - 64-bit variant on page C6-932 Armv8.4 *)
  ; "00  11" => ARM_LDAPURSB (* LDAPURSB - 32-bit variant on page C6-932 Armv8.4 *)
  ; "01  00" => ARM_STLURH (* STLURH Armv8.4 *)
  ; "01  01" => ARM_LDAPURH (* LDAPURH Armv8.4 *)
  ; "01  10" => ARM_LDAPURSH (* LDAPURSH - 64-bit variant on page C6-934 Armv8.4 *)
  ; "01  11" => ARM_LDAPURSH (* LDAPURSH - 32-bit variant on page C6-934 Armv8.4 *)
  ; "10  00" => ARM_STLUR (* STLUR - 32-bit variant on page C6-1219 Armv8.4 *)
  ; "10  01" => ARM_LDAPUR (* LDAPUR - 32-bit variant on page C6-926 Armv8.4 *)
  ; "10  10" => ARM_LDAPURSW (* LDAPURSW Armv8.4 *)
  ; "10  11" => UDF (* Unallocated. - *)
  ; "11  00" => ARM_STLUR (* STLUR - 64-bit variant on page C6-1219 Armv8.4 *)
  ; "11  01" => ARM_LDAPUR (* LDAPUR - 64-bit variant on page C6-926 Armv8.4 *)
  ; "11  10" => UDF (* Unallocated. - *)
  ; "11  11" => UDF (* Unallocated. - *)
  ] else UDF end.


  Definition ld_reg_literal :=
    let opc := n.[30,32] in
    let v_ := n.[26] in 
    match[bits] opc, v_ with
  [ "0   0" => ARM_LDR_LIT (* LDR (literal) - 32-bit variant on page C6-673 *)
  ; "00  1" => ARM_LDR_LIT (* LDR (literal, SIMD&FP) - 32-bit variant on page C7-1362 *)
  ; "01  0" => ARM_LDR_LIT (* LDR (literal) - 64-bit variant on page C6-673 *)
  ; "01  1" => ARM_LDR_LIT (* LDR (literal, SIMD&FP) - 64-bit variant on page C7-1362 *)
  ; "10  0" => ARM_LDRSW_LIT (* LDRSW (literal) *)
  ; "10  1" => ARM_LDR_LIT (* LDR (literal, SIMD&FP) - 128-bit variant on page C7-1362 *)
  ; "11  0" => ARM_PRFM_LIT (* PRFM (literal) *)
  ; "11  1" => UDF (* Unallocated. *)
  ] else UDF end.


  Definition ld_str_no_alloc_pair :=
    let opc := n.[30,32] in
    let v_ := n.[26] in 
    let l_ := n.[22] in
   match[bits] opc, v_, l_ with
  [ "00  0  0" => ARM_STNP (* STNP - 32-bit variant on page C6-865 *)
  ; "00  0  1" => ARM_LDNP (* LDNP - 32-bit variant on page C6-662 *)
  ; "00  1  0" => UDF (* STNP (SIMD&FP) - 32-bit variant on page C7-1626 *)
  ; "00  1  1" => UDF (* LDNP (SIMD&FP) - 32-bit variant on page C7-1353 *)
  ; "01  0  -" => UDF (* Unallocated. *)
  ; "01  1  0" => UDF (* STNP (SIMD&FP) - 64-bit variant on page C7-1626 *)
  ; "01  1  1" => UDF (* LDNP (SIMD&FP) - 64-bit variant on page C7-1353 *)
  ; "10  0  0" => ARM_STNP (* STNP - 64-bit variant on page C6-865 *)
  ; "10  0  1" => ARM_LDNP (* LDNP - 64-bit variant on page C6-662 *)
  ; "0   1  0" => UDF (* STNP (SIMD&FP) - 128-bit variant on page C7-1626 *)
  ; "10  1  1" => UDF (* LDNP (SIMD&FP) - 128-bit variant on page C7-1353 *)
  ; "11  -  -" => UDF (* Unallocated *)
  ] else UDF end.


  Definition ld_str_post_indx_pair :=
    let opc := n.[30,32] in
    let v_ := n.[26] in 
    let l_ := n.[22] in
  match[bits] opc, v_, l_ with
    [ "00  0  0" => ARM_STP (* STP - 32-bit variant on page C6-867 *)
    ; "00  0  1" => ARM_LDP (* LDP - 32-bit variant on page C6-664 *)
    ; "00  1  0" => UDF (* STP (SIMD&FP) - 32-bit variant on page C7-1628 *)
    ; "00  1  1" => UDF (* LDP (SIMD&FP) - 32-bit variant on page C7-1355 *)
    ; "01  0  0" => ARM_STGP (* Armv8.5 *)
    ; "01  0  1" => ARM_LDPSW (* LDPSW *)
    ; "01  1  0" => UDF (* STP (SIMD&FP) - 64-bit variant on page C7-1628 *)
    ; "01  1  1" => UDF (* LDP (SIMD&FP) - 64-bit variant on page C7-1355 *)
    ; "10  0  0" => ARM_STP (* STP - 64-bit variant on page C6-867 *)
    ; "10  0  1" => ARM_LDP (* LDP - 64-bit variant on page C6-664 *)
    ; "10  1  0" => UDF (* STP (SIMD&FP) - 128-bit variant on page C7-1628 *)
    ; "10  1  1" => UDF (* LDP (SIMD&FP) - 128-bit variant on page C7-1355 *)
    ; "11  -  -" => UDF (* Unallocated *)
    ] else UDF end.

  Definition ld_str_pair_offset :=
    let opc := n.[30,32] in
    let v_ := n.[26] in 
    let l_ := n.[22] in
    match[bits] opc, v_, l_ with
  [ "00  0  0" => ARM_STP (* STP - 32-bit variant on page C6-868 *)
  ; "00  0  1" => ARM_LDP (* LDP - 32-bit variant on page C6-665 *)
  ; "00  1  0" => UDF (* STP (SIMD&FP) - 32-bit variant on page C7-1629 *)
  ; "00  1  1" => UDF (* LDP (SIMD&FP) - 32-bit variant on page C7-1356 *)
  ; "01  0  0" => ARM_STGP (* Unallocated. *)
  ; "01  0  1" => ARM_LDPSW (* LDPSW *)
  ; "01  1  0" => UDF (* STP (SIMD&FP) - 64-bit variant on page C7-1629 *)
  ; "01  1  1" => UDF (* LDP (SIMD&FP) - 64-bit variant on page C7-1356 *)
  ; "10  0  0" => ARM_STP (* STP - 64-bit variant on page C6-868 *)
  ; "10  0  1" => ARM_LDP (* LDP - 64-bit variant on page C6-665 *)
  ; "10  1  0" => UDF (* STP (SIMD&FP) - 128-bit variant on page C7-1629 *)
  ; "10  1  1" => UDF (* LDP (SIMD&FP) - 128-bit variant on page C7-1356 *)
  ; "11  -  -" => UDF (* Unallocated. *)
  ] else UDF end.

  Definition ld_str_pre_indx_pair :=
    let opc := n.[30,32] in
    let v_ := n.[26] in 
    let l_ := n.[22] in
    match[bits] opc, v_, l_ with
  [ "00  0  0" => ARM_STP (* STP - 32-bit variant on page C6-867 *)
  ; "00  0  1" => ARM_LDP (* LDP - 32-bit variant on page C6-664 *)
  ; "00  1  0" => UDF (* STP (SIMD&FP) - 32-bit variant on page C7-1628 *)
  ; "00  1  1" => UDF (* LDP (SIMD&FP) - 32-bit variant on page C7-1355 *)
  ; "01  0  0" => ARM_STGP (* Unallocated. *)
  ; "01  0  1" => ARM_LDPSW (* LDPSW *)
  ; "01  1  0" => UDF (* STP (SIMD&FP) - 64-bit variant on page C7-1628 *)
  ; "01  1  1" => UDF (* LDP (SIMD&FP) - 64-bit variant on page C7-1355 *)
  ; "10  0  0" => ARM_STP (* STP - 64-bit variant on page C6-867 *)
  ; "10  0  1" => ARM_LDP (* LDP - 64-bit variant on page C6-664 *)
  ; "10  1  0" => UDF (* STP (SIMD&FP) - 128-bit variant on page C7-1628 *)
  ; "10  1  1" => UDF (* LDP (SIMD&FP) - 128-bit variant on page C7-1355 *)
  ; "11  -  -" => UDF (* Unallocated *)
  ] else UDF end.

  (*unscaled imm*)
  Definition ld_str_reg_imm_u :=
    let size := n.[30,32] in
    let v_ := n.[26] in 
    let opc := n.[22,24] in
  match[bits] size, v_, opc with
  [ "x1  1  1x" => UDF (* Unallocated. *)
  ; "00  0  00" => ARM_STURB (* STURB *)
  ; "00  0  01" => ARM_LDURB (* LDURB *)
  ; "00  0  10" => ARM_LDURSB (* LDURSB - 64-bit variant on page C6-743 *)
  ; "00  0  11" => ARM_LDURSB (* LDURSB - 32-bit variant on page C6-743 *)
  ; "00  1  00" => UDF (* STUR (SIMD&FP) - 8-bit variant on page C7-1638 *)
  ; "00  1  01" => UDF (* LDUR (SIMD&FP) - 8-bit variant on page C7-1367 *)
  ; "00  1  10" => UDF (* STUR (SIMD&FP) - 128-bit variant on page C7-1638 *)
  ; "00  1  11" => UDF (* LDUR (SIMD&FP) - 128-bit variant on page C7-1367 *)
  ; "01  0  00" => ARM_STURH (* STURH *)
  ; "01  0  01" => ARM_LDURH (* LDURH *)
  ; "01  0  10" => ARM_LDURSH (* LDURSH - 64-bit variant on page C6-745 *)
  ; "01  0  11" => ARM_LDURSH (* LDURSH - 32-bit variant on page C6-745 *)
  ; "01  1  00" => UDF (* STUR (SIMD&FP) - 16-bit variant on page C7-1638 *)
  ; "01  1  01" => UDF (* LDUR (SIMD&FP) - 16-bit variant on page C7-1367 *)
  ; "1x  0  11" => UDF (* Unallocated. *)
  ; "1x  1  1x" => UDF (* Unallocated. *)
  ; "10  0  00" => ARM_STUR (* STUR - 32-bit variant on page C6-917 *)
  ; "10  0  01" => ARM_LDUR (* LDUR - 32-bit variant on page C6-739 *)
  ; "10  0  10" => ARM_LDURSW (* LDURSW *)
  ; "10  1  00" => UDF (* STUR (SIMD&FP) - 32-bit variant on page C7-1638 *)
  ; "10  1  01" => UDF (* LDUR (SIMD&FP) - 32-bit variant on page C7-1367 *)
  ; "11  0  00" => ARM_STUR (* STUR - 64-bit variant on page C6-917 *)
  ; "11  0  01" => ARM_LDUR (* LDUR - 64-bit variant on page C6-739 *)
  ; "11  0  10" => ARM_PRFM (* PRFM (unscaled offset) *)
  ; "11  1  00" => UDF (* STUR (SIMD&FP) - 64-bit variant on page C7-1638 *)
  ; "11  1  01" => UDF (* LDUR (SIMD&FP) - 64-bit variant on page C7-1367 *)
  ] else UDF end.

  (*post-indexed imm*)
  Definition ld_str_reg_imm_poi :=
    let size := n.[30,32] in
    let v_ := n.[26] in 
    let opc := n.[22,24] in
  match[bits] size, v_, opc with
  [ "1   1  1x" => UDF (* Unallocated. *)
  ; "00  0  00" => ARM_STRB_IMM (* STRB (immediate) *)
  ; "00  0  01" => ARM_LDRB_IMM (* LDRB (immediate) *)
  ; "00  0  10" => ARM_LDRSB_IMM (* LDRSB (immediate) - 64-bit variant on page C6-685 *)
  ; "00  0  11" => ARM_LDRSB_IMM (* LDRSB (immediate) - 32-bit variant on page C6-685 *)
  ; "00  1  00" => UDF (* STR (immediate, SIMD&FP) - 8-bit variant on page C7-1631 *)
  ; "00  1  01" => UDF (* LDR (immediate, SIMD&FP) - 8-bit variant on page C7-1358 *)
  ; "00  1  10" => UDF (* STR (immediate, SIMD&FP) - 128-bit variant on page C7-1631 *)
  ; "00  1  11" => UDF (* LDR (immediate, SIMD&FP) - 128-bit variant on page C7-1358 *)
  ; "01  0  00" => ARM_STRH_IMM (* STRH (immediate) *)
  ; "01  0  01" => ARM_LDRH_IMM (* LDRH (immediate) *)
  ; "01  0  10" => ARM_LDRSH_IMM (* LDRSH (immediate) - 64-bit variant on page C6-690 *)
  ; "1   0  11" => ARM_LDRSH_IMM (* LDRSH (immediate) - 32-bit variant on page C6-690 *)
  ; "01  1  00" => UDF (* STR (immediate, SIMD&FP) - 16-bit variant on page C7-1631 *)
  ; "01  1  01" => UDF (* LDR (immediate, SIMD&FP) - 16-bit variant on page C7-1358 *)
  ; "1x  0  11" => UDF (* Unallocated. *)
  ; "1x  1  1x" => UDF (* Unallocated. *)
  ; "10  0  00" => ARM_STR_IMM (* STR (immediate) - 32-bit variant on page C6-870 *)
  ; "10  0  01" => ARM_LDR_IMM (* LDR (immediate) - 32-bit variant on page C6-670 *)
  ; "10  0  10" => ARM_LDRSW_IMM (* LDRSW (immediate) *)
  ; "10  1  00" => UDF (* STR (immediate, SIMD&FP) - 32-bit variant on page C7-1631 *)
  ; "10  1  01" => UDF (* LDR (immediate, SIMD&FP) - 32-bit variant on page C7-1358 *)
  ; "11  0  00" => ARM_STR_IMM (* STR (immediate) - 64-bit variant on page C6-870 *)
  ; "11  0  01" => ARM_LDR_IMM (* LDR (immediate) - 64-bit variant on page C6-670 *)
  ; "11  0  10" => UDF (* Unallocated. *)
  ; "11  1  00" => UDF (* STR (immediate, SIMD&FP) - 64-bit variant on page C7-1631 *)
  ; "11  1  01" => UDF (* LDR (immediate, SIMD&FP) - 64-bit variant on page C7-135 *)
  ] else UDF end.

  (*unprivileged*)
  Definition ld_str_reg_unpriv :=
    let size := n.[30,32] in
    let v_ := n.[26] in 
    let opc := n.[22,24] in
  match[bits] size, v_, opc with
  [ "-   1  - " => UDF (* Unallocated. *)
  ; "00  0  00" => ARM_STTRB (* STTRB *)
  ; "00  0  01" => ARM_LDTRB (* LDTRB *)
  ; "00  0  10" => ARM_LDTRSB (* LDTRSB - 64-bit variant on page C6-722 *)
  ; "00  0  11" => ARM_LDTRSB (* LDTRSB - 32-bit variant on page C6-722 *)
  ; "01  0  00" => ARM_STTRH (* STTRH *)
  ; "01  0  01" => ARM_LDTRH (* LDTRH *)
  ; "01  0  10" => ARM_LDTRSH (* LDTRSH - 64-bit variant on page C6-724 *)
  ; "1   0  11" => ARM_LDTRSH (* LDTRSH - 32-bit variant on page C6-724 *)
  ; "1x  0  11" => UDF (* Unallocated. *)
  ; "10  0  00" => ARM_STTR (* STTR - 32-bit variant on page C6-901 *)
  ; "10  0  01" => ARM_LDTR (* LDTR - 32-bit variant on page C6-718 *)
  ; "10  0  10" => ARM_LDTRSW (* LDTRSW *)
  ; "11  0  00" => ARM_STTR (* STTR - 64-bit variant on page C6-901 *)
  ; "11  0  01" => ARM_LDTR (* LDTR - 64-bit variant on page C6-718 *)
  ; "11  0  10" => UDF (* Unallocated. *)
  ] else UDF end.

  (*pre-indexed imm*)
  Definition ld_str_reg_imm_pre  :=
    let size := n.[30,32] in
    let v_ := n.[26] in 
    let opc := n.[22,24] in
  match[bits] size, v_, opc with
  [ "x1  1  1x" => UDF (* Unallocated. *)
  ; "00  0  00" => ARM_STRB_IMM (* STRB (immediate) *)
  ; "00  0  01" => ARM_LDRB_IMM (* LDRB (immediate) *)
  ; "00  0  10" => ARM_LDRSB_IMM (* LDRSB (immediate) - 64-bit variant on page C6-685 *)
  ; "00  0  11" => ARM_LDRSB_IMM (* LDRSB (immediate) - 32-bit variant on page C6-685 *)
  ; "00  1  00" => UDF (* STR (immediate, SIMD&FP) - 8-bit variant on page C7-1631 *)
  ; "00  1  01" => UDF (* LDR (immediate, SIMD&FP) - 8-bit variant on page C7-1358 *)
  ; "00  1  10" => UDF (* STR (immediate, SIMD&FP) - 128-bit variant on page C7-1632 *)
  ; "00  1  11" => UDF (* LDR (immediate, SIMD&FP) - 128-bit variant on page C7-1359 *)
  ; "01  0  00" => ARM_STRH_IMM (* STRH (immediate) *)
  ; "01  0  01" => ARM_LDRH_IMM (* LDRH (immediate) *)
  ; "01  0  10" => ARM_LDRSH_IMM (* LDRSH (immediate) - 64-bit variant on page C6-690 *)
  ; "01  0  11" => ARM_LDRSH_IMM (* LDRSH (immediate) - 32-bit variant on page C6-690 *)
  ; "01  1  00" => UDF (* STR (immediate, SIMD&FP) - 16-bit variant on page C7-1632 *)
  ; "01  1  01" => UDF (* LDR (immediate, SIMD&FP) - 16-bit variant on page C7-1359 *)
  ; "x   0  11" => UDF (* Unallocated. *)
  ; "1x  1  1x" => UDF (* Unallocated. *)
  ; "10  0  00" => ARM_STR_IMM (* STR (immediate) - 32-bit variant on page C6-870 *)
  ; "10  0  01" => ARM_LDR_IMM (* LDR (immediate) - 32-bit variant on page C6-670 *)
  ; "10  0  10" => ARM_LDRSW_IMM (* LDRSW (immediate) *)
  ; "10  1  00" => UDF (* STR (immediate, SIMD&FP) - 32-bit variant on page C7-1632 *)
  ; "10  1  01" => UDF (* LDR (immediate, SIMD&FP) - 32-bit variant on page C7-1359 *)
  ; "11  0  00" => ARM_STR_IMM (* STR (immediate) - 64-bit variant on page C6-870 *)
  ; "11  0  01" => ARM_LDR_IMM (* LDR (immediate) - 64-bit variant on page C6-670 *)
  ; "11  0  10" => UDF (* Unallocated. *)
  ; "11  1  00" => UDF (* STR (immediate, SIMD&FP) - 64-bit variant on page C7-1632 *)
  ; "11  1  01" => UDF (* LDR (immediate, SIMD&FP) - 64-bit variant on page C7-1359 *)
  ] else UDF end.

  (*atomic memory ops*)
  Definition atomic  :=
    let size := n.[30,32] in
    let v_ := n.[26] in 
    let a_ := n.[23] in 
    let r_ := n.[22] in 
    let o3 := n.[15] in 
    let opc := n.[12,15] in
    let rt := n.[0,5] in
  match[bits] size, v_, a_, r_, o3, opc, rt with
  [ "-   0  -  -  1  001  -      " => UDF (* Unallocated. - *)
  ; "-   0  -  -  1  01x  -      " => UDF (* Unallocated. - *)
  ; "-   0  -  -  1  101  -      " => UDF (* Unallocated. - *)
  ; "-   0  -  -  1  11x  -      " => UDF (* Unallocated. - *)
  ; "-   0  0  -  1  100  -      " => UDF (* Unallocated. - *)
  ; "-   0  1  1  1  100  -      " => UDF (* Unallocated. - *)
  ; "-   1  -  -  -  -    -      " => UDF (* Unallocated. - *)
  ; "00  0  0  0  0  000  !=11111" => ARM_LDADDB (* LDADDB, LDADDAB, LDADDALB, LDADDLB - No memory ordering variant on page C6-632 ARMv8.1 *)
  ; "00  0  0  0  0  000  11111  " => ARM_STADDB (* STADDB, STADDLB - No memory ordering variant on *)
  ; "00  0  0  0  0  001  !=11111" => ARM_LDCLRB (* LDCLRB, LDCLRAB, LDCLRALB, LDCLRLB -  *)
  ; "00  0  0  0  0  001  11111  " => ARM_STCLRB (* STCLRB, STCLRLB - ARMv8.1 *)
  ; "00  0  0  0  0  010  !=11111" => ARM_LDEORB (* LDEORB, LDEORAB, LDEORALB, LDEORLB - No *)
  ; "00  0  0  0  0  010  11111  " => ARM_STEORB (* STEORB, STEORLB - ARMv8.1 *)
  ; "00  0  0  0  0  011  !=11111" => ARM_LDSETB (* LDSETB, LDSETAB, LDSETALB, LDSETLB - No *)
  ; "00  0  0  0  0  011  11111  " => ARM_STSETB (* STSETB, STSETLB - ARMv8.1 *)
  ; "00  0  0  0  0  100  !=11111" => ARM_LDSMAXB (* LDSMAXB, LDSMAXAB, LDSMAXALB, LDSMAXLB - ARMv8.1 *)
  ; "00  0  0  0  0  100  11111  " => ARM_STSMAXB (* STSMAXB, STSMAXLB - No memory ordering *)
  ; "00  0  0  0  0  101  !=11111" => ARM_LDSMINB (* LDSMINB, LDSMINAB, LDSMINALB, LDSMINLB *)
  ; "00  0  0  0  0  101  11111  " => ARM_STSMINB (* STSMINB, STSMINLB - No memory ordering variant on page C6-895 *)
  ; "00  0  0  0  0  110  !=11111" => ARM_LDUMAXB (* LDUMAXB, LDUMAXAB, LDUMAXALB, LDUMAXLB - ARMv8.1 *)
  ; "00  0  0  0  0  110  11111  " => ARM_STUMAXB (* STUMAXB, STUMAXLB - No memory ordering *)
  ; "00  0  0  0  0  111  !=11111" => ARM_LDUMINB (* LDUMINB, LDUMINAB, LDUMINALB, LDUMINLB - ARMv8.1 *)
  ; "00  0  0  0  0  111  11111  " => ARM_STUMINB (* STUMINB, STUMINLB - No memory ordering variant *)
  ; "00  0  0  0  1  000  -      " => ARM_SWPB (* SWPB, SWPAB, SWPALB, SWPLB - No memory ordering variant on page C6-941 *)
  ; "00  0  0  1  0  000  !=11111" => ARM_LDADDB (* LDADDB, LDADDAB, LDADDALB, LDADDLB - Release variant on page C6-632 *)
  ; "00  0  0  1  0  000  11111  " => ARM_STADDB (* STADDB, STADDLB - Release variant on page C6-832 *)
  ; "00  0  0  1  0  001  !=11111" => ARM_LDCLRB (* LDCLRB, LDCLRAB, LDCLRALB, LDCLRLB - Release variant on page C6-647 *)
  ; "00  0  0  1  0  001  11111  " => ARM_STCLRB (* STCLRB, STCLRLB - Release variant on page C6-838  *)
  ; "00  0  0  1  0  010  !=11111" => ARM_LDEORB (* LDEORB, LDEORAB, LDEORALB, LDEORLB - *)
  ; "00  0  0  1  0  010  11111  " => ARM_STEORB (* STEORB, STEORLB - Release variant on page C6-844 ARMv8.1 *)
  ; "00  0  0  1  0  011  !=11111" => ARM_LDSETB (* LDSETB, LDSETAB, LDSETALB, LDSETLB - *)
  ; "00  0  0  1  0  011  11111  " => ARM_STSETB (* STSETB, STSETLB - Release variant on page C6-883 ARMv8.1 *)
  ; "00  0  0  1  0  100  !=11111" => ARM_LDSMAXB (* LDSMAXB, LDSMAXAB, LDSMAXALB, *)
  ; "00  0  0  1  0  100  11111  " => ARM_STSMAXB (* STSMAXB, STSMAXLB - Release variant on *)
  ; "00  0  0  1  0  101  !=11111" => ARM_LDSMINB (* LDSMINB, LDSMINAB, LDSMINALB, LDSMINLB *)
  ; "00  0  0  1  0  101  11111  " => ARM_STSMINB (* STSMINB, STSMINLB - Release variant on *)
  ; "00  0  0  1  0  110  !=11111" => ARM_LDUMAXB (* LDUMAXB, LDUMAXAB, LDUMAXALB, LDUMAXLB - Release variant on page C6-727 *)
  ; "00  0  0  1  0  110  11111  " => ARM_STUMAXB (* STUMAXB, STUMAXLB - Release variant on page C6-905 ARMv8.1 *)
  ; "00  0  0  1  0  111  !=11111" => ARM_LDUMINB (* LDUMINB, LDUMINAB, LDUMINALB, LDUMINLB - Release variant on page C6-733 ARMv8.1 *)
  ; "00  0  0  1  0  111  11111  " => ARM_STUMINB (* STUMINB, STUMINLB - Release variant on page C6-911 ARMv8.1 *)
  ; "00  0  0  1  1  000  -      " => ARM_SWPB (* SWPB, SWPAB, SWPALB, SWPLB - Release variant on page C6-941 ARMv8.1 *)
  ; "00  0  1  0  0  000  -      " => ARM_LDADDB (* LDADDB, LDADDAB, LDADDALB, LDADDLB - Acquire variant on page C6-632 ARMv8.1 *)
  ; "00  0  1  0  0  001  -      " => ARM_LDCLRB (* LDCLRB, LDCLRAB, LDCLRALB, LDCLRLB - Acquire variant on page C6-647 ARMv8.1 *)
  ; "00  0  1  0  0  010  -      " => ARM_LDEORB (* LDEORB, LDEORAB, LDEORALB, LDEORLB - Acquire variant on page C6-653 ARMv8.1 *)
  ; "00  0  1  0  0  011  -      " => ARM_LDSETB (* LDSETB, LDSETAB, LDSETALB, LDSETLB - Acquire variant on page C6-700 ARMv8.1 *)
  ; "00  0  1  0  0  100  -      " => ARM_LDSMAXB (* LDSMAXB, LDSMAXAB, LDSMAXALB, LDSMAXLB - Acquire variant on page C6-706 ARMv8.1 *)
  ; "00  0  1  0  0  101  -      " => ARM_LDSMINB (* LDSMINB, LDSMINAB, LDSMINALB, LDSMINLB - Acquire variant on page C6-712 ARMv8.1 *)
  ; "00  0  1  0  0  110  -      " => ARM_LDUMAXB (* LDUMAXB, LDUMAXAB, LDUMAXALB, LDUMAXLB - Acquire variant on page C6-727 ARMv8.1 *)
  ; "00  0  1  0  0  111  -      " => ARM_LDUMINB (* LDUMINB, LDUMINAB, LDUMINALB, LDUMINLB - Acquire variant on page C6-733 *)
  ; "00  0  1  0  1  000  -      " => ARM_SWPB (* SWPB, SWPAB, SWPALB, SWPLB - Acquire varianton page C6-941 *)
  ; "00  0  1  1  0  000  -      " => ARM_LDADDB (* LDADDB, LDADDAB, LDADDALB, LDADDLB - and release variant on page C6-632 *)
  ; "00  0  1  1  0  001  -      " => ARM_LDCLRB (* LDCLRB, LDCLRAB, LDCLRALB, LDCLRLB - and release variant on page C6-647 *)
  ; "00  0  1  1  0  010  -      " => ARM_LDEORB (* LDEORB, LDEORAB, LDEORALB, LDEORLB - and release variant on page C6-653 *)
  ; "00  0  1  1  0  011  -      " => ARM_LDSETB (* LDSETB, LDSETAB, LDSETALB, LDSETLB - and release variant on page C6-700 *)
  ; "00  0  1  1  0  100  -      " => ARM_LDSMAXB (* LDSMAXB, LDSMAXAB, LDSMAXALB,LDSMAXLB - Acquire and release variant on C6-706 *)
  ; "00  0  1  1  0  101  -      " => ARM_LDSMINB (* LDSMINB, LDSMINAB, LDSMINALB, LDSMINLB- Acquire and release variant on page C6-712 *)
  ; "00  0  1  1  0  110  -      " => ARM_LDUMAXB (* LDUMAXB, LDUMAXAB, LDUMAXALB,LDUMAXLB - Acquire and release variant on C6-727 *)
  ; "00  0  1  1  0  111  -      " => ARM_LDUMINB (* LDUMINB, LDUMINAB, LDUMINALB,LDUMINLB - Acquire and release variant on C6-733 *)
  ; "00  0  1  1  1  000  -      " => ARM_SWPB (* SWPB, SWPAB, SWPALB, SWPLB - Acquire and variant on page C6-941 *)
  ; "01  0  0  0  0  000  !=11111" => ARM_LDADDH (* LDADDH, LDADDAH, LDADDALH, LDADDLH - memory ordering variant on page C6-634 *)
  ; "01  0  0  0  0  000  11111  " => ARM_STADDH (* STADDH, STADDLH - No memory ordering variant on C6-834 *)
  ; "01  0  0  0  0  001  !=11111" => ARM_LDCLRH (* LDCLRH, LDCLRAH, LDCLRALH, LDCLRLH - No ordering variant on page C6-649 *)
  ; "01  0  0  0  0  001  11111  " => ARM_STCLRH (* STCLRH, STCLRLH - No memory ordering variant on page C6-840 *)
  ; "01  0  0  0  0  010  !=11111" => ARM_LDEORH (* LDEORH, LDEORAH, LDEORALH, LDEORLH - No memory ordering variant on page C6-655 *)
  ; "01  0  0  0  0  010  11111  " => ARM_STEORH (* STEORH, STEORLH - No memory ordering variant on *)
  ; "01  0  0  0  0  011  !=11111" => ARM_LDSETH (* LDSETH, LDSETAH, LDSETALH, LDSETLH - No *)
  ; "01  0  0  0  0  011  11111  " => ARM_STSETH (* STSETH, STSETLH -  *)
  ; "01  0  0  0  0  100  !=11111" => ARM_LDSMAXH (* LDSMAXH, LDSMAXAH, LDSMAXALH, LDSMAXLH - No memory ordering variant on *)
  ; "01  0  0  0  0  100  11111  " => ARM_STSMAXH (* STSMAXH, STSMAXLH - No memory ordering *)
  ; "01  0  0  0  0  101  !=11111" => ARM_LDSMINH (* LDSMINH, LDSMINAH, LDSMINALH, LDSMINLH *)
  ; "01  0  0  0  0  101  11111  " => ARM_STSMINH (* STSMINH, STSMINLH - No memory ordering variantpage C6-897 *)
  ; "01  0  0  0  0  110  !=11111" => ARM_LDUMAXH (* LDUMAXH, LDUMAXAH, LDUMAXALH, LDUMAXLH - No memory ordering variant on *)
  ; "01  0  0  0  0  110  11111  " => ARM_STUMAXH (* STUMAXH, STUMAXLH - No memory ordering *)
  ; "01  0  0  0  0  111  !=11111" => ARM_LDUMINH (* LDUMINH, LDUMINAH, LDUMINALH, LDUMINLH - No memory ordering variant on *)
  ; "01  0  0  0  0  111  11111  " => ARM_STUMINH (* STUMINH, STUMINLH - No memory ordering varianton .* *)
  ; "01  0  0  0  1  000  -      " => ARM_SWPH (* SWPH, SWPAH, SWPALH, SWPLH - No memory ordering variant on page C6-943 *)
  ; "01  0  0  1  0  000  !=11111" => ARM_LDADDH (* LDADDH, LDADDAH, LDADDALH, LDADDLH - *)
  ; "01  0  0  1  0  000  11111  " => ARM_STADDH (* STADDH, STADDLH - Release variant on *)
  ; "01  0  0  1  0  001  !=11111" => ARM_LDCLRH (* LDCLRH, LDCLRAH, LDCLRALH, LDCLRLH - *)
  ; "01  0  0  1  0  001  11111  " => ARM_STCLRH (* STCLRH, STCLRLH - Release variant on page C6-840 ARMv8.1 *)
  ; "01  0  0  1  0  010  !=11111" => ARM_LDEORH (* LDEORH, LDEORAH, LDEORALH, LDEORLH - *)
  ; "01  0  0  1  0  010  11111  " => ARM_STEORH (* STEORH, STEORLH - Release variant on *)
  ; "01  0  0  1  0  011  !=11111" => ARM_LDSETH (* LDSETH, LDSETAH, LDSETALH, LDSETLH - *)
  ; "01  0  0  1  0  011  11111  " => ARM_STSETH (* STSETH, STSETLH - Release variant on page C6-885 ARMv8.1 *)
  ; "01  0  0  1  0  100  !=11111" => ARM_LDSMAXH (* LDSMAXH, LDSMAXAH, LDSMAXALH,LDSMAXLH - Release variant on page C6-708 *)
  ; "01  0  0  1  0  100  11111  " => ARM_STSMAXH (* STSMAXH, STSMAXLH - Release variant on *)
  ; "01  0  0  1  0  101  !=11111" => ARM_LDSMINH (* LDSMINH, LDSMINAH, LDSMINALH, LDSMINLH *)
  ; "01  0  0  1  0  101  11111  " => ARM_STSMINH (* STSMINH, STSMINLH - Release variant on *)
  ; "01  0  0  1  0  110  !=11111" => ARM_LDUMAXH (* LDUMAXH, LDUMAXAH, LDUMAXALH, LDUMAXLH - Release variant on page C6-729 *)
  ; "01  0  0  1  0  110  11111  " => ARM_STUMAXH (* STUMAXH, STUMAXLH - Release variant on *)
  ; "01  0  0  1  0  111  !=11111" => ARM_LDUMINH (* LDUMINH, LDUMINAH, LDUMINALH, LDUMINLH - Release variant on page C6-735 *)
  ; "01  0  0  1  0  111  11111  " => ARM_STUMINH (* STUMINH, STUMINLH - Release variant on *)
  ; "01  0  0  1  1  000  -      " => ARM_SWPH (* SWPH, SWPAH, SWPALH, SWPLH - Release variant *)
  ; "01  0  1  0  0  000  -      " => ARM_LDADDH (* LDADDH, LDADDAH, LDADDALH, LDADDLH - *)
  ; "01  0  1  0  0  001  -      " => ARM_LDCLRH (* LDCLRH, LDCLRAH, LDCLRALH, LDCLRLH - *)
  ; "01  0  1  0  0  010  -      " => ARM_LDEORH (* LDEORH, LDEORAH, LDEORALH, LDEORLH - *)
  ; "01  0  1  0  0  011  -      " => ARM_LDSETH (* LDSETH, LDSETAH, LDSETALH, LDSETLH - *)
  ; "01  0  1  0  0  100  -      " => ARM_LDSMAXH (* LDSMAXH, LDSMAXAH, LDSMAXALH, LDSMAXLH - Acquire variant on page C6-708 *)
  ; "01  0  1  0  0  101  -      " => ARM_LDSMINH (* LDSMINH, LDSMINAH, LDSMINALH, LDSMINLH *)
  ; "01  0  1  0  0  110  -      " => ARM_LDUMAXH (* LDUMAXH, LDUMAXAH, LDUMAXALH, LDUMAXLH - Acquire variant on page C6-729 *)
  ; "01  0  1  0  0  111  -      " => ARM_LDUMINH (* LDUMINH, LDUMINAH, LDUMINALH, LDUMINLH - Acquire variant on page C6-735 *)
  ; "01  0  1  0  1  000  -      " => ARM_SWPH (* SWPH, SWPAH, SWPALH, SWPLH - Acquire variant *)
  ; "01  0  1  1  0  000  -      " => ARM_LDADDH (* LDADDH, LDADDAH, LDADDALH, LDADDLH - *)
  ; "01  0  1  1  0  001  -      " => ARM_LDCLRH (* LDCLRH, LDCLRAH, LDCLRALH, LDCLRLH - *)
  ; "01  0  1  1  0  010  -      " => ARM_LDEORH (* LDEORH, LDEORAH, LDEORALH, LDEORLH - *)
  ; "01  0  1  1  0  011  -      " => ARM_LDSETH (* LDSETH, LDSETAH, LDSETALH, LDSETLH - *)
  ; "01  0  1  1  0  100  -      " => ARM_LDSMAXH (* LDSMAXH, LDSMAXAH, LDSMAXALH,LDSMAXLH  *)
  ; "01  0  1  1  0  101  -      " => ARM_LDSMINH (* LDSMINH, LDSMINAH, LDSMINALH, LDSMINLH- Acquire and release variant on page C6-714 *)
  ; "01  0  1  1  0  110  -      " => ARM_LDUMAXH (* LDUMAXH, LDUMAXAH, LDUMAXALH, LDUMAXLH - Acquire and release variant on *)
  ; "01  0  1  1  0  111  -      " => ARM_LDUMINH (* LDUMINH, LDUMINAH, LDUMINALH, LDUMINLH - Acquire and release variant on *)
  ; "01  0  1  1  1  000  -      " => ARM_SWPH (* SWPH, SWPAH, SWPALH, SWPLH - Acquire and *)
  ; "10  0  0  0  0  000  !=11111" => ARM_LDADD (* LDADD, LDADDA, LDADDAL, LDADDL - 32-bit, *)
  ; "10  0  0  0  0  000  11111  " => ARM_STADD (* STADD, STADDL - 32-bit, no memory ordering *)
  ; "10  0  0  0  0  001  !=11111" => ARM_LDCLR (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 32-bit, no *)
  ; "10  0  0  0  0  001  11111  " => ARM_STCLR (* STCLR, STCLRL - 32-bit, no memory ordering variant *)
  ; "10  0  0  0  0  010  !=11111" => ARM_LDEOR (* LDEOR, LDEORA, LDEORAL, LDEORL - 32-bit, no *)
  ; "10  0  0  0  0  010  11111  " => ARM_STEOR (* STEOR, STEORL - 32-bit, no memory ordering variant *)
  ; "10  0  0  0  0  011  !=11111" => ARM_LDSET (* LDSET, LDSETA, LDSETAL, LDSETL - 32-bit, no *)
  ; "10  0  0  0  0  011  11111  " => ARM_STSET (* STSET, STSETL - 32-bit, no memory ordering variant *)
  ; "10  0  0  0  0  100  !=11111" => ARM_LDSMAX (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL - 32-bit, no memory ordering variant on page C6-710 *)
  ; "10  0  0  0  0  100  11111  " => ARM_STSMAX (* STSMAX, STSMAXL - 32-bit, no memory ordering *)
  ; "10  0  0  0  0  101  !=11111" => ARM_LDSMIN (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL - 32-bit, no memory ordering variant on page C6-716 *)
  ; "10  0  0  0  0  101  11111  " => ARM_STSMIN (* STSMIN, STSMINL - 32-bit, no memory ordering *)
  ; "10  0  0  0  0  110  !=11111" => ARM_LDUMAX (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL - 32-bit, no memory ordering variant on page C6-731 *)
  ; "10  0  0  0  0  110  11111  " => ARM_STUMAX (* STUMAX, STUMAXL - 32-bit, no memory ordering *)
  ; "10  0  0  0  0  111  !=11111" => ARM_LDUMIN (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL  *)
  ; "10  0  0  0  0  111  11111  " => ARM_STUMIN (* STUMIN, STUMINL - 32-bit, no memory ordering variant on page C6-915 ARMv8.1 *)
  ; "10  0  0  0  1  000  -      " => ARM_SWP (* SWP, SWPA, SWPAL, SWPL - 32-bit, no memory ordering variant on page C6-945 ARMv8.1 *)
  ; "10  0  0  1  0  000  !=11111" => ARM_LDADD (* LDADD, LDADDA, LDADDAL, LDADDL - 32-bit, release variant on page C6-636 ARMv8.1 *)
  ; "10  0  0  1  0  000  11111  " => ARM_STADD (* STADD, STADDL - 32-bit, release variant on page C6-836 ARMv8.1 *)
  ; "10  0  0  1  0  001  !=11111" => ARM_LDCLR (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 32-bit, release variant on page C6-651 ARMv8.1 *)
  ; "10  0  0  1  0  001  11111  " => ARM_STCLR (* STCLR, STCLRL - 32-bit, release variant on page C6-842 ARMv8.1 *)
  ; "10  0  0  1  0  010  !=11111" => ARM_LDEOR (* LDEOR, LDEORA, LDEORAL, LDEORL - 32-bit, release variant on page C6-657 ARMv8.1 *)
  ; "10  0  0  1  0  010  11111  " => ARM_STEOR (* STEOR, STEORL - 32-bit, release variant on page C6-848 ARMv8.1 *)
  ; "10  0  0  1  0  011  !=11111" => ARM_LDSET (* LDSET, LDSETA, LDSETAL, LDSETL - 32-bit, release variant on page C6-704 ARMv8.1 *)
  ; "10  0  0  1  0  011  11111  " => ARM_STSET (* STSET, STSETL - 32-bit, release variant on page C6-887 ARMv8.1 *)
  ; "10  0  0  1  0  100  !=11111" => ARM_LDSMAX (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL - 32-bit, release variant on page C6-710 ARMv8.1 *)
  ; "10  0  0  1  0  100  11111  " => ARM_STSMAX (* STSMAX, STSMAXL - 32-bit, release variant on page C6-893 ARMv8.1 *)
  ; "10  0  0  1  0  101  !=11111" => ARM_LDSMIN (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL - 32-bit, release variant on page C6-716 ARMv8.1 *)
  ; "10  0  0  1  0  101  11111  " => ARM_STSMIN (* STSMIN, STSMINL - 32-bit, release variant on page C6-899 ARMv8.1 *)
  ; "10  0  0  1  0  110  !=11111" => ARM_LDUMAX (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL - 32-bit, release variant on page C6-731 ARMv8.1 *)
  ; "10  0  0  1  0  110  11111  " => ARM_STUMAX (* STUMAX, STUMAXL - 32-bit, release variant on page C6-909 ARMv8.1 *)
  ; "10  0  0  1  0  111  !=11111" => ARM_LDUMIN (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL - 32-bit, release variant on page C6-737 ARMv8.1 *)
  ; "10  0  0  1  0  111  11111  " => ARM_STUMIN (* STUMIN, STUMINL - 32-bit, release variant on page C6-915 ARMv8.1 *)
  ; "10  0  0  1  1  000  -      " => ARM_SWP (* SWP, SWPA, SWPAL, SWPL - 32-bit, release variant on page C6-945 ARMv8.1 *)
  ; "10  0  1  0  0  000  -      " => ARM_LDADD (* LDADD, LDADDA, LDADDAL, LDADDL - 32-bit, *)
  ; "0   0  1  0  0  001  -      " => ARM_LDCLR (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 32-bit, acquire variant on page C6-651 ARMv8.1 *)
  ; "10  0  1  0  0  010  -      " => ARM_LDEOR (* LDEOR, LDEORA, LDEORAL, LDEORL - 32-bit, acquire variant on page C6-657 ARMv8.1 *)
  ; "10  0  1  0  0  011  -      " => ARM_LDSET (* LDSET, LDSETA, LDSETAL, LDSETL - 32-bit, acquire variant on page C6-704 ARMv8.1 *)
  ; "10  0  1  0  0  100  -      " => ARM_LDSMAX (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL - 32-bit, acquire variant on page C6-710 ARMv8.1 *)
  ; "10  0  1  0  0  101  -      " => ARM_LDSMIN (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL - 32-bit, acquire variant on page C6-716 ARMv8.1 *)
  ; "10  0  1  0  0  110  -      " => ARM_LDUMAX (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL - 32-bit, acquire variant on page C6-731 ARMv8.1 *)
  ; "10  0  1  0  0  111  -      " => ARM_LDUMIN (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL - 32-bit, acquire variant on page C6-737 ARMv8.1 *)
  ; "10  0  1  0  1  000  -      " => ARM_SWP (* SWP, SWPA, SWPAL, SWPL - 32-bit, acquire variant on page C6-945 ARMv8.1 *)
  ; "10  0  1  1  0  000  -      " => ARM_LDADD (* LDADD, LDADDA, LDADDAL, LDADDL - 32-bit, acquire and release variant on page C6-636 ARMv8.1 *)
  ; "10  0  1  1  0  001  -      " => ARM_LDCLR (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 32-bit, acquire and release variant on page C6-651 ARMv8.1 *)
  ; "10  0  1  1  0  010  -      " => ARM_LDEOR (* LDEOR, LDEORA, LDEORAL, LDEORL - 32-bit, acquire and release variant on page C6-657 ARMv8.1 *)
  ; "10  0  1  1  0  011  -      " => ARM_LDSET (* LDSET, LDSETA, LDSETAL, LDSETL - 32-bit, acquire and release variant on page C6-704 ARMv8.1 *)
  ; "10  0  1  1  0  100  -      " => ARM_LDSMAX (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL - 32-bit, acquire and release variant on page C6-710 ARMv8.1 *)
  ; "10  0  1  1  0  101  -      " => ARM_LDSMIN (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL - 32-bit, acquire and release variant on page C6-716 ARMv8.1 *)
  ; "10  0  1  1  0  110  -      " => ARM_LDUMAX (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL - 32-bit, acquire and release variant on page C6-731 ARMv8.1 *)
  ; "10  0  1  1  0  111  -      " => ARM_LDUMIN (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL - 32-bit, acquire and release variant on page C6-737 ARMv8.1 *)
  ; "10  0  1  1  1  000  -      " => ARM_SWP (* SWP, SWPA, SWPAL, SWPL - 32-bit, acquire and release variant on page C6-945 ARMv8.1 *)
  ; "11  0  0  0  0  000  !=11111" => ARM_LDADD (* LDADD, LDADDA, LDADDAL, LDADDL - 64-bit, no memory ordering variant on page C6-636 ARMv8.1 *)
  ; "11  0  0  0  0  000  11111  " => ARM_STADD (* STADD, STADDL - 64-bit, no memory ordering variant on page C6-836 ARMv8.1 *)
  ; "11  0  0  0  0  001  !=11111" => ARM_LDCLR (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 64-bit, no memory ordering variant on page C6-651 *)
  ; "1   0  0  0  0  001  11111  " => ARM_STCLR (* STCLR, STCLRL - 64-bit, no memory ordering variant on page C6-842 ARMv8.1 *)
  ; "11  0  0  0  0  010  !=11111" => ARM_LDEOR (* LDEOR, LDEORA, LDEORAL, LDEORL - 64-bit, no memory ordering variant on page C6-657 ARMv8.1 *)
  ; "11  0  0  0  0  010  11111  " => ARM_STEOR (* STEOR, STEORL - 64-bit, no memory ordering variant on page C6-848 ARMv8.1 *)
  ; "11  0  0  0  0  011  !=11111" => ARM_LDSET (* LDSET, LDSETA, LDSETAL, LDSETL - 64-bit, no memory ordering variant on page C6-704 ARMv8.1 *)
  ; "11  0  0  0  0  011  11111  " => ARM_STSET (* STSET, STSETL - 64-bit, no memory ordering variant on page C6-887 ARMv8.1 *)
  ; "11  0  0  0  0  100  !=11111" => ARM_LDSMAX (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL - 64-bit, no memory ordering variant on page C6-710 ARMv8.1 *)
  ; "11  0  0  0  0  100  11111  " => ARM_STSMAX (* STSMAX, STSMAXL - 64-bit, no memory ordering variant on page C6-893 ARMv8.1 *)
  ; "11  0  0  0  0  101  !=11111" => ARM_LDSMIN (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL - 64-bit, no memory ordering variant on page C6-716 ARMv8.1 *)
  ; "11  0  0  0  0  101  11111  " => ARM_STSMIN (* STSMIN, STSMINL - 64-bit, no memory ordering variant on page C6-899 ARMv8.1 *)
  ; "11  0  0  0  0  110  !=11111" => ARM_LDUMAX (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL - 64-bit, no memory ordering variant on page C6-731 ARMv8.1 *)
  ; "11  0  0  0  0  110  11111  " => ARM_STUMAX (* STUMAX, STUMAXL - 64-bit, no memory ordering variant on page C6-909 ARMv8.1 *)
  ; "11  0  0  0  0  111  !=11111" => ARM_LDUMIN (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL - 64-bit, no memory ordering variant on page C6-737 ARMv8.1 *)
  ; "11  0  0  0  0  111  11111  " => ARM_STUMIN (* STUMIN, STUMINL - 64-bit, no memory ordering variant on page C6-915 ARMv8.1 *)
  ; "11  0  0  0  1  000  -      " => ARM_SWP (* SWP, SWPA, SWPAL, SWPL - 64-bit, no memory ordering variant on page C6-945 ARMv8.1 *)
  ; "11  0  0  1  0  000  !=11111" => ARM_LDADD (* LDADD, LDADDA, LDADDAL, LDADDL - 64-bit, release variant on page C6-637 ARMv8.1 *)
  ; "11  0  0  1  0  000  11111  " => ARM_STADD (* STADD, STADDL - 64-bit, release variant on page C6-836 ARMv8.1 *)
  ; "11  0  0  1  0  001  !=11111" => ARM_LDCLR (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 64-bit, release variant on page C6-652 ARMv8.1 *)
  ; "11  0  0  1  0  001  11111  " => ARM_STCLR (* STCLR, STCLRL - 64-bit, release variant on page C6-842 ARMv8.1 *)
  ; "11  0  0  1  0  010  !=11111" => ARM_LDEOR (* LDEOR, LDEORA, LDEORAL, LDEORL - 64-bit,release variant on page C6-658 ARMv8.1 *)
  ; "11  0  0  1  0  010  11111  " => ARM_STEOR (* STEOR, STEORL - 64-bit, release variant on page C6-848 *)
  ; "11  0  0  1  0  011  !=11111" => ARM_LDSET (* LDSET, LDSETA, LDSETAL, LDSETL - 64-bit,release variant on page C6-705 ARMv8.1 *)
  ; "11  0  0  1  0  011  11111  " => ARM_STSET (* STSET, STSETL - 64-bit, release variant on page C6-887 ARMv8.1 *)
  ; "11  0  0  1  0  100  !=11111" => ARM_LDSMAX (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL -64-bit, release variant on page C6-711 ARMv8.1 *)
  ; "11  0  0  1  0  100  11111  " => ARM_STSMAX (* STSMAX, STSMAXL - 64-bit, release variant onpage C6-893 ARMv8.1 *)
  ; "11  0  0  1  0  101  !=11111" => ARM_LDSMIN (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL -64-bit, release variant on page C6-717 ARMv8.1 *)
  ; "11  0  0  1  0  101  11111  " => ARM_STSMIN (* STSMIN, STSMINL - 64-bit, release variant on page C6-899 ARMv8.1 *)
  ; "11  0  0  1  0  110  !=11111" => ARM_LDUMAX (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL -64-bit, release variant on page C6-732 ARMv8.1 *)
  ; "11  0  0  1  0  110  11111  " => ARM_STUMAX (* STUMAX, STUMAXL - 64-bit, release variant onpage C6-909 ARMv8.1 *)
  ; "11  0  0  1  0  111  !=11111" => ARM_LDUMIN (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL - 64-bit, release variant on page C6-738ARMv8.1 *)
  ; "11  0  0  1  0  111  11111  " => ARM_STUMIN (* STUMIN, STUMINL - 64-bit, release variant on page C6-915 ARMv8.1 *)
  ; "11  0  0  1  1  000  -      " => ARM_SWP (* SWP, SWPA, SWPAL, SWPL - 64-bit, release variant on page C6-946 ARMv8.1 *)
  ; "11  0  1  0  0  000  -      " => ARM_LDADD (* LDADD, LDADDA, LDADDAL, LDADDL - 64-bit, acquire variant on page C6-636 ARMv8.1 *)
  ; "11  0  1  0  0  001  -      " => ARM_LDCLR (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 64-bit,acquire variant on page C6-651 ARMv8.1 *)
  ; "11  0  1  0  0  010  -      " => ARM_LDEOR (* LDEOR, LDEORA, LDEORAL, LDEORL - 64-bit, acquire variant on page C6-657 ARMv8.1 *)
  ; "11  0  1  0  0  011  -      " => ARM_LDSET (* LDSET, LDSETA, LDSETAL, LDSETL - 64-bit,acquire variant on page C6-704 ARMv8.1 *)
  ; "11  0  1  0  0  100  -      " => ARM_LDSMAX (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL -64-bit, acquire variant on page C6-710 ARMv8.1 *)
  ; "11  0  1  0  0  101  -      " => ARM_LDSMIN (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL -64-bit, acquire variant on page C6-716 ARMv8.1 *)
  ; "11  0  1  0  0  110  -      " => ARM_LDUMAX (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL -64-bit, acquire variant on page C6-731 ARMv8.1 *)
  ; "11  0  1  0  0  111  -      " => ARM_LDUMIN (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL - 64-bit, acquire variant on page C6-737 ARMv8.1 *)
  ; "11  0  1  0  1  000  -      " => ARM_SWP (* SWP, SWPA, SWPAL, SWPL - 64-bit, acquire varia *)
  ; "1   0  1  1  0  000  -      " => ARM_LDADD (* LDADD, LDADDA, LDADDAL, LDADDL - 64-bit,acquire and release variant on page C6-636 ARMv8.1 *)
  ; "11  0  1  1  0  001  -      " => ARM_LDCLR (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 64-bit,acquire and release variant on page C6-651 ARMv8.1 *)
  ; "11  0  1  1  0  010  -      " => ARM_LDEOR (* LDEOR, LDEORA, LDEORAL, LDEORL - 64-bit,acquire and release variant on page C6-657 ARMv8.1 *)
  ; "11  0  1  1  0  011  -      " => ARM_LDSET (* LDSET, LDSETA, LDSETAL, LDSETL - 64-bit,acquire and release variant on page C6-704 ARMv8.1 *)
  ; "11  0  1  1  0  100  -      " => ARM_LDSMAX (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL -64-bit, acquire and release variant on page C6-710 ARMv8.1 *)
  ; "11  0  1  1  0  101  -      " => ARM_LDSMIN (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL -64-bit, acquire and release variant on page C6-716 ARMv8.1 *)
  ; "11  0  1  1  0  110  -      " => ARM_LDUMAX (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL -64-bit, acquire and release variant on page C6-731 ARMv8.1 *)
  ; "11  0  1  1  0  111  -      " => ARM_LDUMIN (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL -64-bit, acquire and release variant on page C6-737 ARMv8.1 *)
  ; "11  0  1  1  1  000  -      " => ARM_SWP (* SWP, SWPA, SWPAL, SWPL - 64-bit, acquire and release variant on page C6-945 *)
  ] else UDF end.

  (*register offset*)
  Definition ld_str_reg_off  :=
    let opc := n.[22,24] in
    let size := n.[30,32] in
    let v_ := n.[26] in
    let option_ := n.[13,16] in
  match[bits] size, v_, opc, option_ with
  [ "-   -  -   x0x  " => UDF (* Unallocated. *)
  ; "x1  1  1x  -    " => UDF (* Unallocated. *)
  ; "00  0  00  !=011" => ARM_STRB_REG (* STRB (register) - Extended register variant on page C6-877 *)
  ; "00  0  00  011  " => ARM_STRB_REG (* STRB (register) - Shifted register variant on page C6-877 *)
  ; "00  0  01  !=011" => ARM_LDRB_REG (* LDRB (register) - Extended register variant on page C6-679 *)
  ; "00  0  01  011  " => ARM_LDRB_REG (* LDRB (register) - Shifted register variant on page C6-679 *)
  ; "00  0  10  !=011" => ARM_LDRSB_REG (* LDRSB (register) - 64-bit with extended register offset variant on page C6-688 *)
  ; "00  0  10  011  " => ARM_LDRSB_REG (* LDRSB (register) - 64-bit with shifted register offset variant on page C6-688 *)
  ; "00  0  11  !=011" => ARM_LDRSB_REG (* LDRSB (register) - 32-bit with extended register offset variant on page C6-688 *)
  ; "00  0  11  011  " => ARM_LDRSB_REG (* LDRSB (register) - 32-bit with shifted register offset variant on page C6-688 *)
  ; "00  1  00  !=011" => UDF (* STR (register, SIMD&FP) *)
  ; "00  1  00  011  " => UDF (* STR (register, SIMD&FP) *)
  ; "00  1  01  !=011" => UDF (* LDR (register, SIMD&FP) *)
  ; "00  1  01  011  " => UDF (* LDR (register, SIMD&FP) *)
  ; "00  1  10  -    " => UDF (* STR (register, SIMD&FP) *)
  ; "00  1  11  -    " => UDF (* LDR (register, SIMD&FP) *)
  ; "01  0  00  -    " => ARM_STRH_REG (* STRH (register) *)
  ; "01  0  01  -    " => ARM_LDRH_REG (* LDRH (register) *)
  ; "01  0  10  -    " => ARM_LDRSH_REG (* LDRSH (register) - 64-bit variant on page C6-693 *)
  ; "01  0  11  -    " => ARM_LDRSH_REG (* LDRSH (register) - 32-bit variant on page C6-693 *)
  ; "01  1  00  -    " => UDF (* STR (register, SIMD&FP) *)
  ; "01  1  01  -    " => UDF (* LDR (register, SIMD&FP) *)
  ; "1x  0  11  -    " => UDF (* Unallocated. *)
  ; "1x  1  1x  -    " => UDF (* Unallocated. *)
  ; "10  0  00  -    " => ARM_STR_REG (* STR (register) - 32-bit variant on page C6-873 *)
  ; "10  0  01  -    " => ARM_LDR_REG (* LDR (register) - 32-bit variant on page C6-675 *)
  ; "10  0  10  -    " => ARM_LDRSW_REG (* LDRSW (register) *)
  ; "10  1  00  -    " => UDF (* STR (register, SIMD&FP) *)
  ; "10  1  01  -    " => UDF (* LDR (register, SIMD&FP) *)
  ; "11  0  00  -    " => ARM_STR_REG (* STR (register) - 64-bit variant on page C6-873 *)
  ; "11  0  01  -    " => ARM_LDR_REG (* LDR (register) - 64-bit variant on page C6-675 *)
  ; "11  0  10  -    " => ARM_PRFM_REG (* PRFM (register) *)
  ; "11  1  00  -    " => UDF (* STR (register, SIMD&FP) *)
  ; "11  1  01  -    " => UDF (* LDR (register, SIMD&FP) *)
  ] else UDF end.

(*pac*)
  Definition ld_str_reg_pac :=
    let size := n.[30,32] in
    let v_ := n.[26] in 
    let m_ := n.[23] in
    let w_ := n.[11] in
    match[bits] size, v_, m_, w_ with
  [ "!=11  -  -  -" => UDF (* Unallocated. - *)
  ; "11    0  0  0" => ARM_LDRAA_OFFSET (* LDRAA, LDRAB - Key A, offset variant on page C6-983 Armv8.3 *)
  ; "11    0  0  1" => ARM_LDRAA_PRE (* LDRAA, LDRAB - Key A, pre-indexed variant on page C6-983 Armv8.3 *)
  ; "11    0  1  0" => ARM_LDRAA_OFFSET (* LDRAA, LDRAB - Key B, offset variant on page C6-983 Armv8.3 *)
  ; "11    0  1  1" => ARM_LDRAA_PRE (* LDRAA, LDRAB - Key B, pre-indexed variant on page C6-983 Armv8.3 *)
  ; "11    1  -  -" => UDF (* Unallocated. *)
  ] else UDF end.

(*unsigned immediate*)
  Definition ld_str_reg_u_imm  :=
    let opc := n.[22,24] in
    let size := n.[30,32] in
    let v_ := n.[26] in
match[bits] size, v_, opc with
  [ "x1  1  1x" => UDF (* Unallocated. *)
  ; "00  0  00" => ARM_STRB_IMM (* STRB (immediate) *)
  ; "00  0  01" => ARM_LDRB_IMM (* LDRB (immediate) *)
  ; "00  0  10" => ARM_LDRSB_IMM (* LDRSB (immediate) - 64-bit variant on page C6-996 *)
  ; "00  0  11" => ARM_LDRSB_IMM (* LDRSB (immediate) - 32-bit variant on page C6-996 *)
  ; "00  1  00" => UDF (* STR (immediate, SIMD&FP) - 8-bit variant on page C7-2115 *)
  ; "00  1  01" => UDF (* LDR (immediate, SIMD&FP) - 8-bit variant on page C7-1801 *)
  ; "00  1  10" => UDF (* STR (immediate, SIMD&FP) - 128-bit variant on page C7-2116 *)
  ; "00  1  11" => UDF (* LDR (immediate, SIMD&FP) - 128-bit variant on page C7-1802 *)
  ; "01  0  00" => ARM_STRH_IMM (* STRH (immediate) *)
  ; "01  0  01" => ARM_LDRH_IMM (* LDRH (immediate) *)
  ; "01  0  10" => ARM_LDRSH_IMM (* LDRSH (immediate) - 64-bit variant on page C6-1001 *)
  ; "01  0  11" => ARM_LDRSH_IMM (* LDRSH (immediate) - 32-bit variant on page C6-1001 *)
  ; "01  1  00" => UDF (* STR (immediate, SIMD&FP) - 16-bit variant on page C7-2115 *)
  ; "01  1  01" => UDF (* LDR (immediate, SIMD&FP) - 16-bit variant on page C7-1801 *)
  ; "1x  0  11" => UDF (* Unallocated. *)
  ; "1x  1  1x" => UDF (* Unallocated. *)
  ; "10  0  00" => ARM_STR_IMM (* STR (immediate) - 32-bit variant on page C6-1240 *)
  ; "10  0  01" => ARM_LDR_IMM (* LDR (immediate) - 32-bit variant on page C6-977 *)
  ; "10  0  10" => ARM_LDRSW_IMM (* LDRSW (immediate) *)
  ; "10  1  00" => UDF (* STR (immediate, SIMD&FP) - 32-bit variant on page C7-2115 *)
  ; "10  1  01" => UDF (* LDR (immediate, SIMD&FP) - 32-bit variant on page C7-1801 *)
  ; "11  0  00" => ARM_STR_IMM (* STR (immediate) - 64-bit variant on page C6-1240 *)
  ; "11  0  01" => ARM_LDR_IMM (* LDR (immediate) - 64-bit variant on page C6-977 *)
  ; "11  0  10" => ARM_PRFM_IMM (* PRFM (immediate) *)
  ; "11  1  00" => UDF (* STR (immediate, SIMD&FP) - 64-bit variant on page C7-2115 *)
  ; "11  1  01" => UDF (* LDR (immediate, SIMD&FP) - 64-bit variant on page C7-1801 *)
  ] else UDF end.


(** DP REG*)

  (*2 source dp*)
  Definition data_proc_2_src  :=
    let sf := n.[31] in
    let s_ := n.[29] in
    let opcode := n.[10,16] in
    match[bits] sf, s_, opcode with
  [ "-  -  00000x" => UDF (* Unallocated. *)
  ; "-  -  011xxx" => UDF (* Unallocated. *)
  ; "-  -  1xxxxx" => UDF (* Unallocated. *)
  ; "-  0  0001xx" => UDF (* Unallocated. *)
  ; "-  0  0011xx" => UDF (* Unallocated. *)
  ; "-  1  -     " => UDF (* Unallocated. *)
  ; "0  0  000010" => ARM_UDIV (* UDIV - 32-bit variant on page C6-963 *)
  ; "0  0  000011" => ARM_SDIV (* SDIV - 32-bit variant on page C6-823 *)
  ; "0  0  001000" => ARM_LSLV (* LSLV - 32-bit variant on page C6-755 *)
  ; "0  0  001001" => ARM_LSRV (* LSRV - 32-bit variant on page C6-758 *)
  ; "0  0  001010" => ARM_ASRV (* ASRV - 32-bit variant on page C6-546 *)
  ; "0  0  001011" => ARM_RORV (* RORV - 32-bit variant on page C6-814 *)
  ; "0  0  010x11" => UDF (* Unallocated. *)
  ; "0  0  010000" => ARM_CRC32B (* CRC32B, CRC32H, CRC32W, CRC32X - CRC32B variant on page C6-595 *)
  ; "0  0  010001" => ARM_CRC32B (* CRC32B, CRC32H, CRC32W, CRC32X - CRC32H variant on page C6-595 *)
  ; "0  0  010010" => ARM_CRC32B (* CRC32B, CRC32H, CRC32W, CRC32X - CRC32W variant on page C6-595 *)
  ; "0  0  010100" => ARM_CRC32CB (* CRC32CB, CRC32CH, CRC32CW, CRC32CX - CRC32CB variant on page C6-597 *)
  ; "0  0  010101" => ARM_CRC32CB (* CRC32CB, CRC32CH, CRC32CW, CRC32CX - CRC32CH variant on page C6-597 *)
  ; "0  0  010110" => ARM_CRC32CB (* CRC32CB, CRC32CH, CRC32CW, CRC32CX - CRC32CW variant on page C6-597 *)
  ; "1  0  000000" => ARM_SUBP (* SUBP Armv8.5 *)
  ; "1  0  000010" => ARM_UDIV (* UDIV - 64-bit variant on page C6-963 *)
  ; "1  0  000011" => ARM_SDIV (* SDIV - 64-bit variant on page C6-823 *)
  ; "1  0  000100" => ARM_IRG (* IRG Armv8.5 *)
  ; "1  0  000101" => ARM_GMI (* GMI Armv8.5 *)
  ; "1  0  001000" => ARM_LSLV (* LSLV - 64-bit variant on page C6-755 *)
  ; "1  0  001001" => ARM_LSRV (* LSRV - 64-bit variant on page C6-758 *)
  ; "1  0  001010" => ARM_ASRV (* ASRV - 64-bit variant on page C6-546 *)
  ; "1  0  001011" => ARM_RORV (* RORV - 64-bit variant on page C6-814 *)
  ; "1  0  001100" => ARM_PACGA (* PACGA Armv8.3 *)
  ; "1  0  010xx0" => UDF (* Unallocated. *)
  ; "1  0  010x0x" => UDF (* Unallocated. *)
  ; "1  0  010011" => ARM_CRC32B (* CRC32B, CRC32H, CRC32W, CRC32X - CRC32X variant on page C6-595 *)
  ; "1  0  010111" => ARM_CRC32CB (* CRC32CB, CRC32CH, CRC32CW, CRC32CX - CRC32CX variant on page C6-597 *)
  ; "1  1  000000" => ARM_SUBPS (* SUBPS Armv8.5 *)
  ] else UDF end.

  (*1 source*)
  Definition data_proc_1_src  :=
    let sf := n.[31] in
    let s_ := n.[29] in
    let opcode := n.[10,16] in
    let opcode2 := n.[16,21] in
    let rn := n.[5,10] in
 match[bits] sf, s_, opcode2, opcode, rn with
  [ "-  -  -      1xxxxx  -    " => UDF (* Unallocated. - *)
  ; "-  -  xxx1x  -       -    " => UDF (* Unallocated. - *)
  ; "-  -  xx1xx  -       -    " => UDF (* Unallocated. - *)
  ; "-  -  x1xxx  -       -    " => UDF (* Unallocated. - *)
  ; "-  -  1xxxx  -       -    " => UDF (* Unallocated. - *)
  ; "-  0  00000  00011x  -    " => UDF (* Unallocated. - *)
  ; "-  0  00000  001xxx  -    " => UDF (* Unallocated. - *)
  ; "-  0  00000  01xxxx  -    " => UDF (* Unallocated. - *)
  ; "-  1  -      -       -    " => UDF (* Unallocated. - *)
  ; "0  -  00001  -       -    " => UDF (* Unallocated. - *)
  ; "0  0  00000  000000  -    " => ARM_RBIT (* RBIT - 32-bit variant on page C6-1146 - *)
  ; "0  0  00000  000001  -    " => ARM_REV16 (* REV16 - 32-bit variant on page C6-1151 - *)
  ; "0  0  00000  000010  -    " => ARM_REV (* REV - 32-bit variant on page C6-1149 - *)
  ; "0  0  00000  000011  -    " => UDF (* Unallocated. *)
  ; "0  0  00000  000100  -    " => ARM_CLZ (* CLZ - 32-bit variant on page C6-849 - *)
  ; "0  0  00000  000101  -    " => ARM_CLS (* CLS - 32-bit variant on page C6-848 - *)
  ; "1  0  00000  000000  -    " => ARM_RBIT (* RBIT - 64-bit variant on page C6-1146 - *)
  ; "1  0  00000  000001  -    " => ARM_REV16 (* REV16 - 64-bit variant on page C6-1151 - *)
  ; "1  0  00000  000010  -    " => ARM_REV32 (* REV32 - *)
  ; "1  0  00000  000011  -    " => ARM_REV (* REV - 64-bit variant on page C6-1149 - *)
  ; "1  0  00000  000100  -    " => ARM_CLZ (* CLZ - 64-bit variant on page C6-849 - *)
  ; "1  0  00000  000101  -    " => ARM_CLS (* CLS - 64-bit variant on page C6-848 - *)
  ; "1  0  00001  000000  -    " => ARM_PACIA (* PACIA, PACIA1716, PACIASP, PACIAZ, PACIZA - PACIA variant on page C6-1132 Armv8.3 *)
  ; "1  0  00001  000001  -    " => ARM_PACIB (* PACIB, PACIB1716, PACIBSP, PACIBZ, PACIZB - PACIB variant on page C6-1134 Armv8.3 *)
  ; "1  0  00001  000010  -    " => ARM_PACDA (* PACDA, PACDZA - PACDA variant on page C6-1129 Armv8.3 *)
  ; "1  0  00001  000011  -    " => ARM_PACDB (* PACDB, PACDZB - PACDB variant on page C6-1130 Armv8.3 *)
  ; "1  0  00001  000100  -    " => ARM_AUTIA (* AUTIA, AUTIA1716, AUTIASP, AUTIAZ, AUTIZA - AUTIA variant on page C6-793 Armv8.3 *)
  ; "1  0  00001  000101  -    " => ARM_AUTIB (* AUTIB, AUTIB1716, AUTIBSP, AUTIBZ, AUTIZB - AUTIB variant on page C6-795 Armv8.3 *)
  ; "1  0  00001  000110  -    " => ARM_AUTDA (* AUTDA, AUTDZA - AUTDA variant on page C6-791 Armv8.3 *)
  ; "1  0  00001  000111  -    " => ARM_AUTDB (* AUTDB, AUTDZB - AUTDB variant on page C6-792 Armv8.3 *)
  ; "1  0  00001  001000  11111" => ARM_PACIA (* PACIA, PACIA1716, PACIASP, PACIAZ, PACIZA - PACIZA variant on page C6-1132 Armv8.3 *)
  ; "1  0  00001  001001  11111" => ARM_PACIB (* PACIB, PACIB1716, PACIBSP, PACIBZ, PACIZB - PACIZB variant on page C6-1134 Armv8.3 *)
  ; "1  0  00001  001010  11111" => ARM_PACDA (* PACDA, PACDZA - PACDZA variant on page C6-1129 Armv8.3 *)
  ; "1  0  00001  001011  11111" => ARM_PACDB (* PACDB, PACDZB - PACDZB variant on page C6-1130 Armv8.3 *)
  ; "1  0  00001  001100  11111" => ARM_AUTIA (* AUTIA, AUTIA1716, AUTIASP, AUTIAZ, AUTIZA - AUTIZA variant on page C6-793 Armv8.3 *)
  ; "1  0  00001  001101  11111" => ARM_AUTIB (* AUTIB, AUTIB1716, AUTIBSP, AUTIBZ, AUTIZB - AUTIZB variant on page C6-795 Armv8.3 *)
  ; "1  0  00001  001110  11111" => ARM_AUTDA (* AUTDA, AUTDZA - AUTDZA variant on page C6-791 Armv8.3 *)
  ; "1  0  00001  001111  11111" => ARM_AUTDB (* AUTDB, AUTDZB - AUTDZB variant on page C6-792 Armv8.3 *)
  ; "1  0  00001  010000  11111" => ARM_XPACD (* XPACD, XPACI, XPACLRI - XPACI variant on pageC6-1369 Armv8.3 *)
  ; "1  0  00001  010001  11111" => ARM_XPACD (* XPACD, XPACI, XPACLRI - XPACD variant on pageC6-1369 Armv8.3 *)
  ; "1  0  00001  01001x  -    " => UDF (* Unallocated. - *)
  ; "1  0  00001  0101xx  -    " => UDF (* Unallocated. - *)
  ; "1  0  00001  011xxx  -    " => UDF (* Unallocated. *)
  ] else UDF end.


  (*logical - shifted reg*)
  Definition data_proc_logical  :=
    let sf := n.[31] in
    let opc := n.[29,31] in
    let n_ := n.[21] in
    let imm6 := n.[10,16] in
  match[bits] sf, opc, n_, imm6 with
  [ "0  -   -  1xxxxx" => UDF (* Unallocated. *)
  ; "0  00  0  -     " => ARM_AND_SHIFTED (* AND (shifted register) - 32-bit variant on page C6-538 *)
  ; "0  00  1  -     " => ARM_BIC_SHIFTED (* BIC (shifted register) - 32-bit variant on page C6-556 *)
  ; "0  01  0  -     " => ARM_ORR_SHIFTED (* ORR (shifted register) - 32-bit variant on page C6-792 *)
  ; "0  01  1  -     " => ARM_ORN_SHIFTED (* ORN (shifted register) - 32-bit variant on page C6-788 *)
  ; "0  10  0  -     " => ARM_EOR_SHIFTED (* EOR (shifted register) - 32-bit variant on page C6-620 *)
  ; "0  10  1  -     " => ARM_EON_SHIFTED (* EON (shifted register) - 32-bit variant on page C6-617 *)
  ; "0  11  0  -     " => ARM_ANDS_SHIFTED (* ANDS (shifted register) - 32-bit variant on page C6-542 *)
  ; "0  11  1  -     " => ARM_BICS_SHIFTED (* BICS (shifted register) - 32-bit variant on page C6-558 *)
  ; "1  00  0  -     " => ARM_AND_SHIFTED (* AND (shifted register) - 64-bit variant on page C6-538 *)
  ; "1  00  1  -     " => ARM_BIC_SHIFTED (* BIC (shifted register) - 64-bit variant on page C6-556 *)
  ; "1  01  0  -     " => ARM_ORR_SHIFTED (* ORR (shifted register) - 64-bit variant on page C6-792 *)
  ; "1  01  1  -     " => ARM_ORN_SHIFTED (* ORN (shifted register) - 64-bit variant on page C6-788 *)
  ; "1  10  0  -     " => ARM_EOR_SHIFTED (* EOR (shifted register) - 64-bit variant on page C6-620 *)
  ; "1  10  1  -     " => ARM_EON_SHIFTED (* EON (shifted register) - 64-bit variant on page C6-617 *)
  ; "1  11  0  -     " => ARM_ANDS_SHIFTED (* ANDS (shifted register) - 64-bit variant on page C6-542 *)
  ; "1  11  1  -     " => ARM_BICS_SHIFTED (* BICS (shifted register) - 64-bit variant on page C6-558 *)
  ] else UDF end.


  (*add/sub - shifted reg*)
  Definition add_sub_shifted  :=
    let sf := n.[31] in
    let op := n.[30] in
    let s_ := n.[29] in
    let shift := n.[22,24] in
    let imm6 := n.[10,16] in
  match[bits] sf, opc, s_, shift, imm6 with
    [ "-  -  -  11  -     " => UDF (* Unallocated. *)
    ; "0  -  -  -   1xxxxx" => UDF (* Unallocated. *)
    ; "0  0  0  -   -     " => ARM_ADD_SHIFTED (* ADD (shifted register) - 32-bit variant on page C6-527 *)
    ; "0  0  1  -   -     " => ARM_ADDS_SHIFTED (* ADDS (shifted register) - 32-bit variant on page C6-533 *)
    ; "0  1  0  -   -     " => ARM_SUB_SHIFTED (* SUB (shifted register) - 32-bit variant on page C6-932 *)
    ; "0  1  1  -   -     " => ARM_SUBS_SHIFTED (* SUBS (shifted register) - 32-bit variant on page C6-938 *)
    ; "1  0  0  -   -     " => ARM_ADD_SHIFTED (* ADD (shifted register) - 64-bit variant on page C6-527 *)
    ; "1  0  1  -   -     " => ARM_ADDS_SHIFTED (* ADDS (shifted register) - 64-bit variant on page C6-533 *)
    ; "1  1  0  -   -     " => ARM_SUB_SHIFTED (* SUB (shifted register) - 64-bit variant on page C6-932 *)
    ; "1  1  1  -   -     " => ARM_SUBS_SHIFTED (* SUBS (shifted register) - 64-bit variant on page C6-938 *)
    ] else UDF end.

  (*add/sub - extended reg*)
  Definition add_sub_extended  :=
    let sf := n.[31] in
    let op := n.[30] in
    let s_ := n.[29] in
    let imm3 := n.[10,16] in
    match[bits] sf, opc, s_, opt, imm3 with
  [ "-  -  -  -   1x1" => UDF (* Unallocated. *)
  ; "-  -  -  -   11x" => UDF (* Unallocated. *)
  ; "-  -  -  x1  -  " => UDF (* Unallocated. *)
  ; "-  -  -  1x  -  " => UDF (* Unallocated. *)
  ; "0  0  0  00  -  " => ARM_ADD_EXTENDED (* ADD (extended register) - 32-bit variant on page C6-523 *)
  ; "0  0  1  00  -  " => ARM_ADDS_EXTENDED (* ADDS (extended register) - 32-bit variant on page C6-529 *)
  ; "0  1  0  00  -  " => ARM_SUB_EXTENDED (* SUB (extended register) - 32-bit variant on page C6-928 *)
  ; "0  1  1  00  -  " => ARM_SUBS_EXTENDED (* SUBS (extended register) - 32-bit variant on page C6-934 *)
  ; "1  0  0  00  -  " => ARM_ADD_EXTENDED (* ADD (extended register) - 64-bit variant on page C6-523 *)
  ; "1  0  1  00  -  " => ARM_ADDS_EXTENDED (* ADDS (extended register) - 64-bit variant on page C6-529 *)
  ; "1  1  0  00  -  " => ARM_SUB_EXTENDED (* SUB (extended register) - 64-bit variant on page C6-928 *)
  ; "1  1  1  00  -  " => ARM_SUBS_EXTENDED (* SUBS (extended register) - 64-bit variant on page C6-934 *)
  ] else UDF end.

  (*add/sub - with carry*)
  Definition add_sub_carry  :=
    let sf := n.[31] in
    let op := n.[30] in
    let s_ := n.[29] in
    let opcode2 := n.[10,16] in
    match[bits] sf, opc, s_, opcode2 with
  [ "-  -  -  xxxxx1" => UDF (* Unallocated. *)
  ; "-  -  -  xxxx1x" => UDF (* Unallocated. *)
  ; "-  -  -  xxx1xx" => UDF (* Unallocated. *)
  ; "-  -  -  xx1xxx" => UDF (* Unallocated. *)
  ; "-  -  -  x1xxxx" => UDF (* Unallocated. *)
  ; "-  -  -  1xxxxx" => UDF (* Unallocated. *)
  ; "0  0  0  000000" => ARM_ADC (* ADC - 32-bit variant on page C6-521 *)
  ; "0  0  1  000000" => ARM_ADCS (* ADCS - 32-bit variant on page C6-522 *)
  ; "0  1  0  000000" => ARM_SBC (* SBC - 32-bit variant on page C6-815 *)
  ; "0  1  1  000000" => ARM_SBCS (* SBCS - 32-bit variant on page C6-817 *)
  ; "1  0  0  000000" => ARM_ADC (* ADC - 64-bit variant on page C6-521 *)
  ; "1  0  1  000000" => ARM_ADCS (* ADCS - 64-bit variant on page C6-522 *)
  ; "1  1  0  000000" => ARM_SBC (* SBC - 64-bit variant on page C6-815 *)
  ; "1  1  1  000000" => ARM_SBCS (* SBCS - 64-bit variant on page C6-817 *)
  ] else UDF end.

  (*rotate right into flags*)
  Definition rotate  :=
    let sf := n.[31] in
    let op := n.[30] in
    let s_ := n.[29] in
    let o2 := n.[4] in
    match[bits] sf, op, s_, o2 with
  [ "0  -  -  -" => UDF (* Unallocated. - *)
  ; "1  0  0  -" => UDF (* Unallocated. - *)
  ; "1  0  1  0" => ARM_RMIF (* RMIF Armv8.4 *)
  ; "1  0  1  1" => UDF (* Unallocated. - *)
  ; "1  1  -  -" => UDF (* Unallocated. - *)
  ] else UDF end.

  (*evaluate into flags*)
  Definition evaluate  :=
    let sf := n.[31] in
    let op := n.[30] in
    let s_ := n.[29] in
    let opcode2 := n.[15,21] in
    let sz := n.[14] in
    let o3 := n.[4] in
    let mask := n.[0,4] in
    match[bits] sf, op, s_, opcode2, sz, o3, mask with
  [ "0  0  0  -         -  -  -     " => UDF (* Unallocated. - *)
  ; "0  0  1  !=000000  -  -  -     " => UDF (* Unallocated. - *)
  ; "0  0  1  000000    -  0  !=1101" => UDF (* Unallocated. - *)
  ; "0  0  1  000000    -  1  -     " => UDF (* Unallocated. - *)
  ; "0  0  1  000000    0  0  1101  " => ARM_SETF8 (* SETF8, SETF16 - SETF8 variant on page C6-1175 Armv8.4 *)
  ; "0  0  1  000000    1  0  1101  " => ARM_SETF8 (* SETF8, SETF16 - SETF16 variant on page C6-1175 Armv8.4 *)
  ; "0  1  -  -         -  -  -     " => UDF (* Unallocated. - *)
  ; "1  -  -  -         -  -  -     " => UDF (* Unallocated. *)
  ] else UDF end.

  (*conditional compare immediate*)
  Definition cond_compare :=
    let sf := n.[31] in
    let op := n.[30] in
    let s_ := n.[29] in
    let o2 := n.[10] in 
    let o3 := n.[4] in
    match[bits] sf, op, s_, o2, o3 with
  [ "-  -  -  -  1" => UDF (* Unallocated. *)
  ; "-  -  -  1  -" => UDF (* Unallocated. *)
  ; "-  -  0  -  -" => UDF (* Unallocated. *)
  ; "0  0  1  0  0" => ARM_CCMN_IMM (* CCMN (immediate) - 32-bit variant on page C6-833 *)
  ; "0  1  1  0  0" => ARM_CCMP_IMM (* CCMP (immediate) - 32-bit variant on page C6-837 *)
  ; "1  0  1  0  0" => ARM_CCMN_IMM (* CCMN (immediate) - 64-bit variant on page C6-833 *)
  ; "1  1  1  0  0" => ARM_CCMP_IMM (* CCMP (immediate) - 64-bit variant on page C6-837 *)
  ] else UDF end.
  
  (*conditional select*)
  Definition cond_compare :=
    let sf := n.[31] in
    let op := n.[30] in
    let s_ := n.[29] in
    let op2 := n.[10,12] in 
    match[bits] sf, op, s_, op2 with
  [ "-  -  -  1x" => UDF (* Unallocated. *)
  ; "-  -  1  - " => UDF (* Unallocated. *)
  ; "0  0  0  00" => ARM_CSEL (* CSEL - 32-bit variant on page C6-871 *)
  ; "0  0  0  01" => ARM_CSINC (* CSINC - 32-bit variant on page C6-877 *)
  ; "0  1  0  00" => ARM_CSINV (* CSINV - 32-bit variant on page C6-879 *)
  ; "0  1  0  01" => ARM_CSNEG (* CSNEG - 32-bit variant on page C6-881 *)
  ; "1  0  0  00" => ARM_CSEL (* CSEL - 64-bit variant on page C6-871 *)
  ; "1  0  0  01" => ARM_CSINC (* CSINC - 64-bit variant on page C6-877 *)
  ; "1  1  0  00" => ARM_CSINV (* CSINV - 64-bit variant on page C6-879 *)
  ; "1  1  0  01" => ARM_CSNEG (* CSNEG - 64-bit variant on page C6-881 *)
  ] else UDF end.

  (*3 source dp*)
  Definition data_proc_3_src  :=    
    let sf := n.[31] in
    let op54 := n.[29,31] in
    let op31 := n.[21,24] in
    let o0 := n.[15] in 
    match[bits] sf, op54, op31, o0 with
  [ "-  00  010  1" => UDF (* Unallocated. *)
  ; "-  00  011  -" => UDF (* Unallocated. *)
  ; "-  00  100  -" => UDF (* Unallocated. *)
  ; "-  00  110  1" => UDF (* Unallocated. *)
  ; "-  00  111  -" => UDF (* Unallocated. *)
  ; "-  01  -    -" => UDF (* Unallocated. *)
  ; "-  1x  -    -" => UDF (* Unallocated. *)
  ; "0  00  000  0" => ARM_MADD (* MADD - 32-bit variant on page C6-1085 *)
  ; "0  00  000  1" => ARM_MSUB (* MSUB - 32-bit variant on page C6-1109 *)
  ; "0  00  001  0" => UDF (* Unallocated. *)
  ; "0  00  001  1" => UDF (* Unallocated. *)
  ; "0  00  010  0" => UDF (* Unallocated. *)
  ; "0  00  101  0" => UDF (* Unallocated. *)
  ; "0  00  101  1" => UDF (* Unallocated. *)
  ; "0  00  110  0" => UDF (* Unallocated. *)
  ; "1  00  000  0" => ARM_MADD (* MADD - 64-bit variant on page C6-1085 *)
  ; "1  00  000  1" => ARM_MSUB (* MSUB - 64-bit variant on page C6-1109 *)
  ; "1  00  001  0" => ARM_SMADDL (* SMADDL *)
  ; "1  00  001  1" => ARM_SMSUBL (* SMSUBL *)
  ; "1  00  010  0" => ARM_SMULH (* SMULH *)
  ; "1  00  101  0" => ARM_UMADDL (* UMADDL *)
  ; "1  00  101  1" => ARM_UMSUBL (* UMSUBL *)
  ; "1  00  110  0" => ARM_UMULH (* UMULH *)
  ] else UDF end.

  Definition dp_fp_simd := UDF.

  Definition decode :=
    let op0 := n.[25,29] in
    match[bits] op0 with
      [ "0000" => UDF (* Reserved *)
      ; "0001" => UDF (* Unallocated. *)
      ; "0010" => UDF (* SVE Instructions. See SVE on page A2-92 *)
      ; "0011" => UDF (* Unallocated. *)
      ; "100x" => dp_imm (* Data Processing -- Immediate *)
      ; "101x" => branch_exc (* Branches, Exception Generating and System instructions on page C4-257 *)
      ; "x1x0" => load_store (* Loads and Stores on page C4-266 *)
      ; "x101" => dp_reg (* Data Processing -- Register on page C4-299 *)
      ; "x111" => dp_fp_simd (* Data Processing -- Scalar Floating-Point and Advanced SIMD on page C4-309 *)
      ] else UDF end.
End Decoder.
