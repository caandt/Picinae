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
  (*TODO: do these two need to be control flow/branch specific?*)
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
  | ARM_UNDEFINED
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
  | ARM_STP_POST
  | ARM_LDP
  | ARM_LDPSW
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
      [ "0  0" => B_cond (* B.cond *)
      ; "0  1" => UDF (* Unallocated. *)
      ; "1  -" => UDF (* Unallocated. *)
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
      ; "100  000  - " => UDF (* Unallocated. *)
      ; "101  000  00" => UDF (* Unallocated. *)
      ; "101  000  01" => ARM_DCPS1 (* DCPS1 *)
      ; "101  000  10" => ARM_DCPS2 (* DCPS2 *)
      ; "101  000  11" => ARM_DCPS3 (* DCPS3 *)
      ; "110  000  - " => UDF (* Unallocated. *)
      ; "111  000  - " => UDF (* Unallocated. *)
      ] else UDF end.
  Definition hints :=
    let CRm := n.[8,12] in
    let op2 := n.[5,8] in
    match[bits] CRm, op2 with
      [ "-     -  " => UDF (* HINT - *)
      ; "0000  000" => ARM_NOP (* NOP - *)
      ; "0000  001" => UDF (* YIELD - *)
      ; "0000  010" => ARM_WFE (* WFE - *)
      ; "0000  011" => ARM_WFI (* WFI - *)
      ; "0000  100" => ARM_SEV (* SEV - *)
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
  Definition sys_reg_move :=
    let L := n.[21] in
    match[bits] L with
      [ "0" => UDF (* MSR (register) *)
      ; "1" => UDF (* MRS *)
      ] else UDF end.
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
      [ "010  0xxxxxxxxxxxxx  -    " => cond_branch (* Conditional branch (immediate) *)
      ; "110  00xxxxxxxxxxxx  -    " => exc_gen (* Exception generation on page C4-272 *)
      ; "110  01000000110010  11111" => hints (* Hints on page C4-272 *)
      ; "110  01000000110011  -    " => barriers (* Barriers on page C4-274 *)
      ; "110  0100000xxx0100  -    " => pstate (* PSTATE on page C4-274 *)
      ; "110  0100x01xxxxxxx  -    " => sys_inst (* System instructions on page C4-275 *)
      ; "110  0100x1xxxxxxxx  -    " => sys_reg_move (* System register move on page C4-275 *)
      ; "110  1xxxxxxxxxxxxx  -    " => uncond_b_reg (* Unconditional branch (register) on page C4-275 *)
      ; "x00  -               -    " => uncond_b_imm (* Unconditional branch (immediate) on page C4-278 *)
      ; "x01  0xxxxxxxxxxxxx  -    " => comp_and_b (* Compare and branch (immediate) on page C4-279 *)
      ; "x01  1xxxxxxxxxxxxx  -    " => test_and_b (* Test and branch (immediate) on page C4-279 *)
      ] else UDF end.

  Definition load_store := UDF.
  Definition dp_reg := UDF.
  Definition dp_fp_simd := UDF.

  Definition decode :=
    let op0 := n.[25,29] in
    match[bits] op0 with
      [ "0000" => UDF (* Reserved *)
      ; "0001" => UDF (* Unallocated. *)
      ; "0010" => UDF (* SVE Instructions. See The Scalable Vector Extension (SVE) on page A2-99. *)
      ; "0011" => UDF (* Unallocated. *)
      ; "100x" => dp_imm (* Data Processing -- Immediate *)
      ; "101x" => branch_exc (* Branches, Exception Generating and System instructions on page C4-271 *)
      ; "x1x0" => load_store (* Loads and Stores on page C4-279 *)
      ; "x101" => dp_reg (* Data Processing -- Register on page C4-310 *)
      ; "x111" => dp_fp_simd (* Data Processing -- Scalar Floating-Point and Advanced SIMD on page C4-320 *)
      ] else UDF end.
End Decoder.
