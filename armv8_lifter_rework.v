(*
   Armv8-A A64 lifter based on issue E.a
   https://developer.arm.com/documentation/ddi0487/ea/
 *)
Set Printing Depth 50.
Set Printing Width 100.
Unset Printing All.


Require Import Picinae_armv8_pcode Picinae_armv8_PIL_notation.
Import Picinae_armv8_PIL_notation.Notation.
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
  Definition parse_pattern pat := let (s, e) := match pat with
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
  Notation "pats => val" := (pats, val) (at level 201).
  Notation "'match[bits]' n0 , .. , nn 'with' | c0 | .. | cn 'else' d 'end'" := (
     match n0::..[nn].., c0::..[cn].. with ns, cases =>
       ltac:(let r := eval cbn in (select_pattern_list ns d cases) in exact r)
     end
  ) (at level 0, c0 at level 201, only parsing).


  Notation "n .[ i , j ]" := (xbits n i j) (at level 30, format "n .[ i , j ]").
  Notation "n .[ b ]" := (xbits n b (b+1)) (at level 30, format "n .[ b ]").

  (* ARMv8 Constants *)
  Notation "'LOG2_TAG_GRANULE'" := (4) (at level 0, only parsing).
End Notation.
Import Notation.

Notation "'PCvar'" := (R_PC) (in custom PIL at level 65).
Notation "'PC'" := (Var R_PC) (in custom PIL at level 65).

(* Assume we are in Execution Level 0 (User mode). NB. This simplifies some of the pseudocode. *)
(*  J1-7341
    bits(64) sp = SP[];
    stack_align_check = (SCTLR[].SA0 != '0')
    if stack_align_check && sp != Align(sp, 16) then SPAlignmentFault()
    return;
  *)

Definition XtoVar n := let n := <{n#5}> in <{
  ite (n = (0#5)) {Var R_X0} ( ite (n = (1#5)) {Var R_X1} ( ite (n = (2#5)) {Var R_X2} ( ite (n = (3#5)) {Var R_X3} (
  ite (n = (4#5)) {Var R_X4} ( ite (n = (5#5)) {Var R_X5} ( ite (n = (6#5)) {Var R_X6} ( ite (n = (7#5)) {Var R_X7} (
  ite (n = (8#5)) {Var R_X8} ( ite (n = (9#5)) {Var R_X9} ( ite (n = (10#5)) {Var R_X10} ( ite (n = (11#5)) {Var R_X11} (
  ite (n = (12#5)) {Var R_X12} ( ite (n = (13#5)) {Var R_X13} ( ite (n = (14#5)) {Var R_X14} ( ite (n = (15#5)) {Var R_X15} (
  ite (n = (16#5)) {Var R_X16} ( ite (n = (17#5)) {Var R_X17} ( ite (n = (18#5)) {Var R_X18} ( ite (n = (19#5)) {Var R_X19} (
  ite (n = (20#5)) {Var R_X20} ( ite (n = (21#5)) {Var R_X21} ( ite (n = (22#5)) {Var R_X22} ( ite (n = (23#5)) {Var R_X23} (
  ite (n = (24#5)) {Var R_X24} ( ite (n = (25#5)) {Var R_X25} ( ite (n = (26#5)) {Var R_X26} ( ite (n = (27#5)) {Var R_X27} (
  ite (n = (28#5)) {Var R_X28} ( ite (n = (29#5)) {Var R_X29} ( ite (n = (30#5)) {Var R_X30} {Var R_SP}))))))))))))))))))))))))))))))
}>.

Definition arm_varid n :=
  match n with
  | 0 => R_X0 | 1 => R_X1 | 2 => R_X2 | 3 => R_X3 | 4 => R_X4 | 5 => R_X5 | 6 => R_X6 | 7 => R_X7
  | 8 => R_X8 | 9 => R_X9 | 10 => R_X10 | 11 => R_X11 | 12 => R_X12 | 13 => R_X13 | 14 => R_X14 | 15 => R_X15
  | 16 => R_X16 | 17 => R_X17 | 18 => R_X18 | 19 => R_X19 | 20 => R_X20 | 21 => R_X21 | 22 => R_X22 | 23 => R_X23
  | 24 => R_X24 | 25 => R_X25 | 26 => R_X26 | 27 => R_X27 | 28 => R_X28 | 29 => R_X29 | 30 => R_X30
  | _ => R_SP
  end.

  Definition Unpack_NZCV (flags : exp) : exp * exp * exp * exp :=
  (* Shift each bit down to the 0th position and mask it out with 1 *)
  let n := Cast CAST_LOW 1 (BinOp OP_AND (BinOp OP_RSHIFT flags (Word 3 4)) (Word 1 4)) in
  let z := Cast CAST_LOW 1 (BinOp OP_AND (BinOp OP_RSHIFT flags (Word 2 4)) (Word 1 4)) in
  let c := Cast CAST_LOW 1 (BinOp OP_AND (BinOp OP_RSHIFT flags (Word 1 4)) (Word 1 4)) in
  let v := Cast CAST_LOW 1 (BinOp OP_AND flags (Word 1 4)) in

  (* Return them as a 4-tuple tuple of expressions *)
  (n, z, c, v).


Notation "'var[' n ']'" := (arm_varid n) (in custom PIL at level 65, no associativity).
Notation "'X[' n ']'" := (XtoVar n) (in custom PIL at level 65, no associativity).
Notation "'Xtemp[' n ']'" := (Var (V_TEMP n)) (in custom PIL at level 65, no associativity).
Notation "'Xtemp[' n ']'" := (Var (V_TEMP n)) (at level 65, no associativity).
Notation "'temp[' n ']'" := (V_TEMP n) (in custom PIL at level 65, no associativity).
Notation "'temp[' n ']'" := (V_TEMP n) (at level 65, no associativity).

Definition arm_assign_R n val := Move (arm_varid n) val. (*TODO: Need to fix this*)
Definition arm_assign_flags flags :=
    let '(n, z, c, v) := Unpack_NZCV flags in
    
    (Seq (Move R_NG n) (Seq (Move R_ZR z) (Seq (Move R_CY c) (Move R_OV v)))).

Definition arm64_R n N :=
     if (N =? 32) then Cast CAST_LOW 32 (Var (arm_varid n))
     else Var (arm_varid n).
(*x is data size := 32/64*)
Notation "R[ n , x ]" := (arm64_R n x) (at level 0).

Definition SP_read w := <{lcast w {Var R_SP} }>.
Definition SP_write e : stmt := <{R_SP := ucast 64 e }>.
Definition b2exp b := match b with true => Word 1 1 | false => Word 0 1 end.


Definition AllocationTagFromAddress e := <{e[59:56]}>. (* AArch64.AllocationTagFromAddress *)
Notation "'AllocTag' e" := (AllocationTagFromAddress e) (in custom PIL at level 65, no associativity).

Definition AlignPow2 e w pow2 := match pow2 with
                                | 1 =>      e
                                | 2 =>   <{ e >> (1 # w) << 1 # w }>
                                | 4 =>   <{ e >> (2 # w) << 2 # w }>
                                | 8 =>   <{ e >> (3 # w) << 3 # w }>
                                | 16 =>  <{ e >> (4 # w) << 4 # w }>
                                | 32 =>  <{ e >> (5 # w) << 5 # w }>
                                | 64 =>  <{ e >> (6 # w) << 6 # w }>
                                | 128 => <{ e >> (7 # w) << 7 # w }>
                                | 256 => <{ e >> (8 # w) << 8 # w }>
                                | _ =>      e  (* No good sentinel value *)
                                end.
Notation "'Align[' e , w , pow2 ']'" := (AlignPow2 e w pow2) (in custom PIL at level 65, no associativity).

(* Checks whether w-bit e is a multiple of alignment. *)
Definition AlignCheck e w alignment := <{ e % (alignment # w) = (0 # w) }>.
Notation "'Aligned[' e , w , alignment ']'" := (AlignCheck e w alignment) (in custom PIL at level 65, no associativity).
Notation "'Aligned[' e , alignment ']'" := (AlignCheck e 64 alignment) (in custom PIL at level 65, no associativity).
Notation "'TagAligned[' e ']'" := (AlignCheck e 64 16) (in custom PIL at level 65, no associativity).

Definition CheckSPAlignment :=
  <{ if {Var SCTLR_E1}[4] & ! TagAligned[{Var R_SP}] then exn 0 else nop end}>.

(* Assume AllocationTagAccess is disabled, just turn off the tag bits 59:56. *)
Definition AddressWithAllocationTag (Xt tag:exp) := <{
  (Xt & (! 0x0F00_0000_0000_0000 # 64))
}>.

(* J1-7339 *)
Definition MemSingleWrite address size (val:exp) := <{
  (* assert size in {1, 2, 4, 8, 16} omitted *)
  if Aligned[ address, 64, size ] then nop else exn 0 end;
  store[address, val, LittleE, size]
}>.

(* J1-7342 *)
Definition MemWrite address size val := MemSingleWrite address size val.

(* J1-7341 *)
Definition MemRead address size := <{load[address, LittleE, size]}>.

(* Addr - 64bits; tag - 4bits *)
(* We do not model tag memory, this is a no-op if the address is aligned. *)
Definition MemTagWrite (addr tag:exp) := <{
  if ! TagAligned[addr] then exn 0 else nop end
  (* Assumption: address translation does not abort nor raise a debug exception *)
}>.
(* Addr - 64bits *)
(* We do not model tag memory, this just returns the tagging-disabled value. *)
Definition MemTagRead (addr:exp) := <{ 0 # 4 }>.

Notation "'Z'" := (Var R_ZR) (in custom PIL at level 0).
Notation "'N'" := (Var R_NG) (in custom PIL at level 0).
Notation "'C'" := (Var R_CY) (in custom PIL at level 0).
Notation "'V'" := (Var R_OV) (in custom PIL at level 0).

Definition ConditionHolds (cond:N) : exp :=
  let case := <{cond#4[3:1]}> in
  let EQ_NE := <{case = 0#3}> in
  let CS_CC := <{case = 1#3}> in
  let MI_PL := <{case = 2#3}> in
  let VS_VC := <{case = 3#3}> in
  let HI_LS := <{case = 4#3}> in
  let GE_LT := <{case = 5#3}> in
  let GT_LE := <{case = 6#3}> in
  let AL    := <{case = 7#3}> in
  <{ite (cond#4 = 0xF#4) 1#1
      (cond#4[0] ^ (* First bit negates condition *)
        (ite EQ_NE (Z=1#1) (
        ite CS_CC (C=1#1) (
        ite MI_PL (N=1#1) (
        ite VS_VC (V=1#1) (
        ite HI_LS (C=1#1 & Z = 0#1) (
        ite GE_LT (N=V) (N=V & Z=0#1))))))))
  }>.

(* Assume LittleE only execution. The documentation for Big Endian
   is a little confusing and sparse (J1-7567). *)
Definition BigEndian : exp := <{0#0}>.

(* Configure Atomic extension, for now it seems to be supportable.
   We do not model concurrency so these are just regular operations. *)
Definition HaveAtomicExt : exp := <{1#1}>.

Definition havoc := <{ exn 0 }>.

Definition UsingAArch32 := <{ {Var R_nRW} = 1#1 }>.
Definition BranchTo w target := <{
  if (w#w = 32#w) then
    if UsingAArch32 then jmp (ucast 64 target) else exn 0 end
  else
    if (w#w = 64#w) & !UsingAArch32 then jmp target else exn 0 end
  end
}>.

Notation "'branch' e" := (BranchTo 64 e) (in custom PIL at level 0, e at level 99).

(* ARM does not provide a bit encoding for these atomic operations, but 9 are
    listed in the MemAtomic auxiliary function. We just use 0-8, but it is arbitrary. *)
Notation "'MemAtomicOp_ADD'" := (<{0#5}>) (in custom PIL at level 0).
Notation "'MemAtomicOp_BIC'" := (<{1#5}>) (in custom PIL at level 0).
Notation "'MemAtomicOp_EOR'" := (<{2#5}>) (in custom PIL at level 0).
Notation "'MemAtomicOp_ORR'" := (<{3#5}>) (in custom PIL at level 0).
Notation "'MemAtomicOp_SMAX'" := (<{4#5}>) (in custom PIL at level 0).
Notation "'MemAtomicOp_SMIN'" := (<{5#5}>) (in custom PIL at level 0).
Notation "'MemAtomicOp_UMAX'" := (<{6#5}>) (in custom PIL at level 0).
Notation "'MemAtomicOp_UMIN'" := (<{7#5}>) (in custom PIL at level 0).
Notation "'MemAtomicOp_SWP'" := (<{8#5}>) (in custom PIL at level 0).
Notation "'MemAtomicOp_ADD'" := (<{0#5}>) (at level 0).
Notation "'MemAtomicOp_BIC'" := (<{1#5}>) (at level 0).
Notation "'MemAtomicOp_EOR'" := (<{2#5}>) (at level 0).
Notation "'MemAtomicOp_ORR'" := (<{3#5}>) (at level 0).
Notation "'MemAtomicOp_SMAX'" := (<{4#5}>) (at level 0).
Notation "'MemAtomicOp_SMIN'" := (<{5#5}>) (at level 0).
Notation "'MemAtomicOp_UMAX'" := (<{6#5}>) (at level 0).
Notation "'MemAtomicOp_UMIN'" := (<{7#5}>) (at level 0).
Notation "'MemAtomicOp_SWP'" := (<{8#5}>) (at level 0).

(*DP Imm - C4.1.2, page C4-252*)
(*Add/Sub*)
Variant arm_add_sub_imm :=
  | ARM_ADD_IMM
  | ARM_ADDS_IMM
  | ARM_SUB_IMM
  | ARM_SUBS_IMM.
(*Logical (imm), Bitfield*)
Variant arm_logical_imm :=
  | ARM_AND_IMM 
  | ARM_ANDS_IMM
  | ARM_EOR_IMM
  | ARM_ORR_IMM
  | ARM_BFM_IMM 
  | ARM_SBFM_IMM 
  | ARM_UBFM_IMM.
(*Move (imm)*)
Variant arm_move_imm :=
  | ARM_MOVZ_IMM
  | ARM_MOVN_IMM
  | ARM_MOVK_IMM.
(*DP Register - C4.1.5, page C4-299*)
(*Add/Sub, Logical, Bitwise Shifted*)
Variant arm_data_shifted :=
  | ARM_ADD_SHIFTED_REG
  | ARM_ADDS_SHIFTED_REG
  | ARM_SUB_SHIFTED_REG
  | ARM_SUBS_SHIFTED_REG.

Variant arm_log_shifted :=
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
  | ARM_MOV_LOG_REG.
(*Add/Sub Extended*)
Variant arm_extended :=
  | ARM_ADD_EXTENDED_REG
  | ARM_ADDS_EXTENDED_REG
  | ARM_SUB_EXTENDED_REG
  | ARM_SUBS_EXTENDED_REG.
(*Add/Sub With Carry*)
Variant arm_carry :=
  | ARM_ADC 
  | ARM_ADCS 
  | ARM_SBC 
  | ARM_SBCS.
(*Shift Register*)
Variant arm_shift_reg :=
  | ARM_ASRV_REG 
  | ARM_LSLV_REG 
  | ARM_LSRV_REG 
  | ARM_RORV_REG.
(*Bitops*)
Variant arm_bitops :=
  | ARM_CLS  
  | ARM_CLZ  
  | ARM_RBIT 
  | ARM_REV  
  | ARM_REV16
  | ARM_REV32
  | ARM_REV64.
(*Loads and Stores*)
Variant arm_load_gen :=
  (*LDAPR/STLR unscaled immediate*)
  | ARM_STLURB      | ARM_LDAPURB
  | ARM_LDAPURSB    | ARM_STLURH
  | ARM_LDAPURH     | ARM_LDAPURSH
  | ARM_LDAPUR      | ARM_LDAPURSW
  | ARM_STLUR       | ARM_PRFM
  | ARM_PRFM_IMM 
  (*load/store register (unscaled immediate)*)
  | ARM_STURB       | ARM_LDURB
  | ARM_LDURSB      | ARM_STURH
  | ARM_LDURH       | ARM_LDURSH
  | ARM_STUR        | ARM_LDUR
  | ARM_LDURSW.
(*Atomic*)
Variant arm_atomic :=
  | ARM_LDADDB      | ARM_LDCLRB 
  | ARM_LDEORB      | ARM_LDSETB 
  | ARM_LDSMAXB     | ARM_LDSMINB 
  | ARM_LDUMAXB     | ARM_LDUMINB 
  | ARM_SWPB        | ARM_LDADDH 
  | ARM_LDCLRH      | ARM_LDEORH 
  | ARM_LDSETH      | ARM_LDSMAXH 
  | ARM_LDSMINH     | ARM_LDUMAXH 
  | ARM_LDUMINH     | ARM_SWPH
  | ARM_LDADD       | ARM_LDCLR 
  | ARM_LDEOR       | ARM_LDSET 
  | ARM_LDSMAX      | ARM_LDSMIN
  | ARM_LDUMAX      | ARM_LDUMIN
  | ARM_SWP         | ARM_LDAPRB
  | ARM_LDAPRH      | ARM_LDAPR. 
Variant arm_ldstr_reg :=
  | ARM_STRB_REG 
  | ARM_LDRB_REG 
  | ARM_LDRSB_REG 
  | ARM_STRH_REG 
  | ARM_LDRH_REG 
  | ARM_LDRSH_REG 
  | ARM_STR_REG 
  | ARM_LDR_REG 
  | ARM_LDRSW_REG 
  | ARM_PRFM_REG.
Variant arm_unpriv :=
  | ARM_STTRB 
  | ARM_LDTRB 
  | ARM_LDTRSB 
  | ARM_STTRH 
  | ARM_LDTRH 
  | ARM_LDTRSH 
  | ARM_STTR 
  | ARM_LDTR 
  | ARM_LDTRSW. 
Variant arm_indexed :=
  | ARM_STRB_IMM 
  | ARM_LDRB_IMM 
  | ARM_LDRSB_IMM 
  | ARM_LDR_IMM 
  | ARM_STRH_IMM 
  | ARM_LDRH_IMM 
  | ARM_LDRSH_IMM 
  | ARM_STR_IMM 
  | ARM_LDRSW_IMM. 
Variant arm_ld_reg_lit :=
  | ARM_LDR_LIT 
  | ARM_LDRSW_LIT
  | ARM_PRFM_LIT.
Variant arm_ldstr_reg_pair :=
  | ARM_STP
  | ARM_LDP
  | ARM_LDPSW
  | ARM_STGP. 
Variant arm_exclusive :=
  | ARM_STXRB       | ARM_STLXRB 
  | ARM_LDXRB       | ARM_LDXRH 
  | ARM_LDAXRB      | ARM_STLLRB 
  | ARM_STLLRH      | ARM_STLRH 
  | ARM_STLRB       | ARM_STXRH 
  | ARM_STLXRH      | ARM_LDLARB
  | ARM_LDARB       | ARM_LDARH
  | ARM_LDLARH      | ARM_STXR 
  | ARM_STLXR       | ARM_STXP 
  | ARM_STLXP       | ARM_LDXR 
  | ARM_LDAXR       | ARM_LDXP 
  | ARM_LDAXP       | ARM_STLLR
  | ARM_STLR        | ARM_LDLAR
  | ARM_LDAR        | ARM_CASP 
  | ARM_CASB        | ARM_CASH
  | ARM_CAS         | ARM_LDAXRH.
Variant inst :=
(*DP imm*)
  | ARM_DATA_IMM (op: arm_add_sub_imm) (sf s sh imm12 Rn Rd : N)
  (*v8.5: with tag, not implemented : ARM_ADDG, ARM_SUBG*)    
  | ARM_LOGICAL_IMM (op: arm_logical_imm) (Rn Rd immr imms sf n_:N)
  | ARM_MOVE_IMM (op: arm_move_imm) (Rd imm16 size shift:N)
  (*| TODO: ARM_MOV_IMM bitmask imm/wide imm/inverted wide imm*)
  (*PC relative addr*)
  | ARM_ADRP_IMM
  | ARM_ADR_IMM
  (*extract*)
  | ARM_EXTRACT
  | ARM_EXTEND (op: arm_extended) (sf s opt Rm option_ imm3 Rn Rd : N)
  (*conditional comparison*)
  | ARM_CCMN_IMM (sf Rn imm nzcv cond:N)
  | ARM_CCMP_IMM (sf Rn imm nzcv cond:N)
(*DP reg*)
  | ARM_EXTENDED (op: arm_extended) (sf s opt Rm option_ imm3 Rn Rd : N)
  | ARM_DATA_SHIFTED (op: arm_data_shifted) (sf s shift Rm imm6 Rn Rd :N)
  | ARM_LOG_SHIFTED (op: arm_log_shifted) (sf shift Rm imm6 Rn Rd :N)
  | ARM_CARRY (op: arm_carry) (sf s Rm Rn Rd :N)
  | ARM_SHIFT (op: arm_shift_reg) (sf Rm op2 Rn Rd :N)
  | ARM_BITOPS (op: arm_bitops) (sf Rn Rd:N)
  (*rotate*)
  | ARM_RMIF
  (*conditional select*)
  | ARM_CSEL
  | ARM_CSINV
  | ARM_CSNEG
  | ARM_CSETM
  (*conditional comparison*)
  | ARM_CCMN_REG (sf Rm cond Rn nzcv:N)
  | ARM_CCMP_REG (sf Rm cond Rn nzcv:N)
  | ARM_CSINC
  (*mul/div reg*)
  | ARM_MADD (*TODO: mults only*)
  | ARM_MSUB
  | ARM_SMADDL
  | ARM_SMSUBL
  | ARM_SMULH
  | ARM_UMADDL
  | ARM_UMSUBL
  | ARM_UMULH
  | ARM_SDIV (*Not implemented bc of Reals*)
  | ARM_UDIV (*Not implemented bc of Reals*)
  (*crc32*)
  | ARM_CRC32B
  | ARM_CRC32H
  | ARM_CRC32W
  | ARM_CRC32X
  | ARM_CRC32CB
  | ARM_CRC32CH
  | ARM_CRC32CW
  | ARM_CRC32CX
(*Branches*)
  (* decoding not implemented yet, treat as unpredictable *)
  | idk
  | ARM_UNPREDICTABLE
  | UDF (*ARM_UNDEFINED*)
  (*hints*)
  | ARM_HINT
  | ARM_XPACD
  | ARM_PACIA
  | ARM_PACIB
  | ARM_AUTIA
  | ARM_AUTIB
  | ARM_PSB_CSYNC
  | ARM_TSB_CSYNC
  | ARM_CSDB
  | ARM_BTI
  | ARM_SB
  (*conditional branch (imm)*)
  | ARM_B_COND (cond imm19:N)
  (*exception generation*)
  | ARM_SVC
  | ARM_HVC
  | ARM_SMC
  | ARM_BRK
  | ARM_HLT
  | ARM_DCPS1
  | ARM_DCPS2
  | ARM_DCPS3
  (*system, pstate*)
  | ARM_NOP
  | ARM_YIELD
  | ARM_WFE
  | ARM_WFI
  | ARM_SEV
  | ARM_SEVL
  | ARM_ESB
  | ARM_CLREX
  | ARM_DSB
  | ARM_DMB
  | ARM_ISB
  | ARM_SYS
  | ARM_MSR
  | ARM_MSR_IMM
  | ARM_MSR_REG
  | ARM_CFINV
  | ARM_SYSL
  | ARM_MRS
  | ARM_SSBB
  | ARM_PSSBB
  | ARM_XAFLAG
  | ARM_AXFLAG
  (*unconditional branch(register)*)
  | ARM_BR (Xn:N)
  | ARM_BLR (Xn:N)
  | ARM_RET (Xn:N)
  | ARM_ERET
  | ARM_DRPS
  | ARM_BRAAZ (Xn:N)
  | ARM_BRAA_REG
  | ARM_BLRAA_REG
  | ARM_BLRAAZ
  | ARM_RETAA
  | ARM_ERETAA
  (*unconditional branch(imm)*)
  | ARM_B (imm26:N)
  | ARM_BL (imm26:N)
  (*compare and branch(imm)*)
  | ARM_CBZ (Rt imm19 size:N)
  | ARM_CBNZ (Rt imm19 size:N)
  (*test and branch(imm)*)
  | ARM_TBZ (Rt imm14 b5 b40:N)
  | ARM_TBNZ (Rt imm14 b5 b40:N)

(*Loads and Stores*)
  (*exclusive/others*)
  | ARM_EXCLUSIVE (op: arm_exclusive) (size Xn Xs Xt Xt2:N)
  (*bunch of variants for these, refer to page C4-230*)
  (*LDAPR/STLR unscaled immediate*)
  | ARM_LOAD_GEN (op: arm_load_gen) (Xn Xt imm9 size:N)
  (*load/store memory tags*)
  | ARM_STG (Xn Xt imm9:N) (writeback printindex:bool)
  | ARM_STZG (Xn Xt imm9:N) (writeback printindex:bool)
  | ARM_STZGM (Xn Xt:N)
  | ARM_LDG (Xn Xt imm9:N)
  | ARM_ST2G (Xn Xt imm9:N) (writeback printindex:bool)
  | ARM_STGM (Xn Xt:N)
  | ARM_STZ2G (Xn Xt imm9:N) (writeback printindex:bool)
  | ARM_LDGM (Xn Xt:N)
  (*load register (literal)*)
  | ARM_LD_REG_LIT (op: arm_ld_reg_lit) (Xt imm19 size:N)
  (*load/store no-allocate pair (offset)*)
  | ARM_STNP (Xn Xt Xt2 imm7 scale:N)
  | ARM_LDNP (Xn Xt Xt2 imm7 scale:N)
  (*load/store register pair (post-indexed, pre-indexed, offset)*)
  | ARM_LD_STR_REG_PAIR (op: arm_ldstr_reg_pair) (Xn Xt Xt2 imm7 scale:N) (wback postindex:bool)
  | ARM_PFRM
  (*imm pre/post-indexed*)
  | ARM_INDEXED (op: arm_indexed) (Xn Xt imm912 size:N) (signed wback postindex:bool)
  (*register unprivileged*)
  | ARM_REG_UNPRIVILEGED (op: arm_unpriv) (Rn Rt imm9 size:N)
  (*atomic memory ops*)
  | ARM_ATOMIC (op:arm_atomic) (size Xn Xs Xt:N)
  (*there's a lot more here, not sure how much to add. Pages C4-240-250*)
  (*pac*)
  | ARM_LDRAA (Xn Xt S imm9:N) (wback:bool)
  (*load/store register*)
  | ARM_LD_STR_REG (op:arm_ldstr_reg)  (Xn Xm Xt extend size S:N)
  (*TODO: There are way more load instructions than written out here, add to this section plz*)
(*Data Processing*)
  (*2 src*)
  | ARM_LSLV
  | ARM_LSRV
  | ARM_ASRV
  | ARM_RORV
  | ARM_SUBP
  | ARM_IRG
  | ARM_GMI
  | ARM_PACGA
  | ARM_SUBPS
  (*1 src*)
  | ARM_PACDA
  | ARM_PACDB
  | ARM_AUTDA
  | ARM_AUTDB
  (*evaluate*)
  | ARM_SETF8
  .

(* Returns index in Xtemp[300], returns 0 for no-bits set, thus it is ambiguous.
    Clobber Xtemp[301].

    NB. We can embed HighestSetBit in a PIL expression rather than a statement
    if we know the bitwidth beforehand. Just use a sequence of nested ites.
    This already assumes a max iwdth of 64 bits. *)
Definition HighestSetBit w e := <{
  temp[301] := w#w - 1#w;
  rep w#w do if (1#w<<Xtemp[301] & e) <> 0#w then nop else temp[301] := Xtemp[301] - 1#w end end;
  temp[300] := Xtemp[301]
}>.

Print HighestSetBit.

(* Return a w-bit expression of e ones *)
Definition Ones w e := <{
  (1#w << e) - 1#w
}>.

Definition ROR w x shift := <{ite (shift#w = 0#w) x ((x >> shift#w) | (x << (w#w-shift#w)))}>.

(* Replicate w-bit expression x until it is w' bits *)
Definition Replicate rettemp t w w' x := <{
  if w'#w' % w#w' <> 0#w' then exn 0 else nop end;
  temp[t] := 0#w;
  temp[rettemp] := 0#w';
  rep w'#w' / w#w' do temp[rettemp] := Xtemp[rettemp] | ((ucast w' x) << ((ucast w' Xtemp[t]) * w'#w')); temp[t] := Xtemp[t]+1#w end
}>.

(* J1-7389 *)
(* Writes the M-bit wmask and tmask into temp[980] and temp[990]. *)
  Definition DecodeBitMasks (immN imms immr immediate M:N) :=
    let imms := <{imms#6}> in
    let immr := <{immr#6}> in
    let immN := Word immN 1 in
    let immediate := Word immediate 1 in
    let immNNOTimms := <{immN ++ imms}> in
    let levels := <{Xtemp[400]}> in
    let S := <{Xtemp[401]}> in
    let R := <{Xtemp[402]}> in
    let lenw7 := <{Xtemp[300]}> in (* len <= 6 *)
    let lenw6 := <{Xtemp[301]}> in (* len <= 6 *)
    let esize := <{Xtemp[404]}> in
    let d := <{Xtemp[405]}> in
    <{
      (* lenw7 *) 
      {HighestSetBit 7 immNNOTimms};
      (* The highest setbit position of w bits is w-1;
          casting the len down to 6-bits does not lose information
          and is useful below. *)
      (* lenw6 *) temp[301] := lcast 6 lenw7;
      if Xtemp[300] < 1#7 then exn 0 else nop end;
      if M#64 < (1#64 << ucast 64 Xtemp[300]) then exn 0 else nop end;
      (* levels *) temp[400] := {Ones 6 lenw6};
      if immediate & (imms & levels = levels) then exn 0 else nop end;
      (* S *) temp[401] := imms & levels;
      (* R *) temp[402] := immr & levels;
      (* diff *) temp[403] := S-R;
      (* esize *) temp[404] := 1#7 << lenw7;
      (* d *) temp[405] := Xtemp[403] & levels;
      if lenw6 = 1#6 then
      (* welem *) temp[410] := {Ones 2 (Cast CAST_LOW 2 (BinOp OP_PLUS (Var (V_TEMP 401)) (Word 1 6)))};
      (* telem *) temp[411] := {Ones 2 <{lcast {2} ({d} + {1}#{6})}>};
      (* wmask *) {Replicate 980 406 2 M <{Xtemp[410]}>};
      (* tmask *) {Replicate 990 406 2 M <{Xtemp[411]}>} else
      if lenw6 = 2#6 then
      (* welem *) temp[410] := {Ones 4 <{lcast {4} ({S} + {1}#{6})}>};
      (* telem *) temp[411] := {Ones 4 <{lcast {4} ({d} + {1}#{6})}>};
      (* wmask *) {Replicate 980 406 4 M <{Xtemp[410]}>};
      (* tmask *) {Replicate 990 406 4 M <{Xtemp[411]}>} else
      if lenw6 = 3#6 then
      (* welem *) temp[410] := {Ones 8 <{ucast {8} ({S} + {1}#{6})}>};
      (* telem *) temp[411] := {Ones 8 <{ucast {8} ({d} + {1}#{6})}>};
      (* wmask *) {Replicate 980 406 8 M <{Xtemp[410]}>};
      (* tmask *) {Replicate 990 406 8 M <{Xtemp[411]}>} else
      if lenw6 = 4#6 then
      (* welem *) temp[410] := {Ones 16 <{ucast {16} ({S} + {1}#{6})}>};
      (* telem *) temp[411] := {Ones 16 <{ucast {16} ({d} + {1}#{6})}>};
      (* wmask *) {Replicate 980 406 16 M <{Xtemp[410]}>};
      (* tmask *) {Replicate 990 406 16 M <{Xtemp[411]}>} else
      if lenw6 = 5#6 then
      (* welem *) temp[410] := {Ones 32 <{ucast {32} ({S} + {1}#{6})}>};
      (* telem *) temp[411] :=  {Ones 32 <{ucast {32} ({d} + {1}#{6})}>};
      (* wmask *) {Replicate 980 406 32 M <{Xtemp[410]}>};
      (* tmask *) {Replicate 990 406 32 M <{Xtemp[411]}>} else
      if lenw6 = 6#6 then
      (*M cannot be 32 here*)
      (* welem *) temp[410] := {Ones 64 <{ucast {64} ({S} + {1}#{6})}>};
      (* telem *) temp[411] := {Ones 64 <{ucast {64} ({d} + {1}#{6})}>};
      (* wmask *) {Replicate 980 406 64 64 <{Xtemp[410]}>};
      (* tmask *) {Replicate 990 406 64 64 <{Xtemp[411]}>} else
      exn 0 end end end end end end
  }>.

Section Decoder.
  Variable n : N.

(** DP Immediate*)
  Definition pc_rel :=
    let op := n.[31] in
    match[bits] op with
    | "0" => ARM_ADR_IMM (* ADR *)
    | "1" => ARM_ADRP_IMM (* ADRP *)
    else UDF end.

  Definition add_sub_imm :=
    let sf := n.[31] in
    let op := n.[30] in
    let s := n.[29] in
    let sh := n.[22] in
    let imm12 := n.[10,22] in
    let Rn := n.[5,10] in let Rd := n.[0,5] in
    match[bits] sf, op, s with
    | "0  0  0" => ARM_DATA_IMM ARM_ADD_IMM sf s sh imm12 Rn Rd  (* ADD (immediate) - 32-bit variant on page C6-761 *)
    | "0  0  1" => ARM_DATA_IMM ARM_ADDS_IMM sf s sh imm12 Rn Rd (* ADDS (immediate) - 32-bit variant on page C6-769 *)
    | "0  1  0" => ARM_DATA_IMM ARM_SUB_IMM sf s sh imm12 Rn Rd (* SUB (immediate) - 32-bit variant on page C6-1311 *)
    | "0  1  1" => ARM_DATA_IMM ARM_SUBS_IMM sf s sh imm12 Rn Rd (* SUBS (immediate) - 32-bit variant on page C6-1321 *)
    | "1  0  0" => ARM_DATA_IMM ARM_ADD_IMM sf s sh imm12 Rn Rd (* ADD (immediate) - 64-bit variant on page C6-761 *)
    | "1  0  1" => ARM_DATA_IMM ARM_ADDS_IMM sf s sh imm12 Rn Rd (* ADDS (immediate) - 64-bit variant on page C6-769 *)
    | "1  1  0" => ARM_DATA_IMM ARM_SUB_IMM sf s sh imm12 Rn Rd (* SUB (immediate) - 64-bit variant on page C6-1311 *)
    | "1  1  1" => ARM_DATA_IMM ARM_SUBS_IMM sf s sh imm12 Rn Rd (* SUBS (immediate) - 64-bit variant on page C6-1321 *)  
    else UDF end.

(**  (*immediate, with tags*)
  Definition add_sub_imm_tags :=
    let sf := n.[31] in
    let op := n.[30] in
    let s_ := n.[29] in
    match[bits] sf, op, s_ with
    | "0  -  -" => UDF (* Unallocated. - *)
    | "1  -  1" => UDF (* Unallocated. - *)
    | "1  0  0" => ARM_ADDG (* ADDG Armv8.5 *)
    | "1  1  0" => ARM_SUBG (* SUBG Armv8.5 *)
    else UDF end. *)

  Definition arm_ands_imm2il (Xn Xd immr imms sf n:N) :=
    let bit32variant := <{sf#1 = 0#1 & n#1 = 0#1}> in
    let datasize := (if sf =? 1 then 64 else 32) in
    let imm := <{Xtemp[980]}> in
    let UNDEF := <{ (sf#1 = 0#1 & n#1 <> 0#1) }> in
    <{
      if UNDEF then exn 0 else nop end;
      {DecodeBitMasks n imms immr 1 datasize};
      (* imm: temp[980] *)
      (* operand1 *) temp[1000] := lcast datasize X[Xn];
      (* result *) {arm_varid Xd} := Xtemp[1000] & imm;
      R_NG := X[Xd][{datasize-1}];
      R_ZR := X[Xd] = 0#64;
      R_CY := 0#1;
      R_OV := 0#1
    }>.

  Definition arm_and_imm2il (Xn Xd immr imms sf n:N) :=
    let bit32variant := <{sf#1 = 0#1 & n#1 = 0#1}> in
    let datasize := (if sf =? 1 then 64 else 32) in
    let imm := <{Xtemp[980]}> in
    let UNDEF := <{ (sf#1 = 0#1 & n#1 <> 0#1) }> in
    <{
      if UNDEF then exn 0 else nop end;
      {DecodeBitMasks n imms immr 1 datasize};
      (* imm: temp[980] *)
      (* operand1 *) temp[1000] := lcast datasize X[Xn];
       {arm_varid Xd} := ucast 64 (Xtemp[1000] & imm)
    }>.

  Definition arm_eor_imm2il (Xn Xd immr imms sf n:N) :=
    let bit32variant := <{sf#1 = 0#1 & n#1 = 0#1}> in
    let datasize := (if sf =? 1 then 64 else 32) in
    let imm := <{Xtemp[980]}> in
    let UNDEF := <{ (sf#1 = 0#1 & n#1 <> 0#1) }> in
    <{
      if UNDEF then exn 0 else nop end;
      {DecodeBitMasks n imms immr 1 datasize};
      (* imm: temp[980] *)
      {arm_varid Xd} := X[Xn] ^ imm
    }>.

  Definition arm_orr_imm2il (Xn Xd immr imms sf n:N) :=
    let bit32variant := <{sf#1 = 0#1 & n#1 = 0#1}> in
    let datasize := (if sf =? 1 then 64 else 32) in
    let imm := <{Xtemp[980]}> in
    let UNDEF := <{ (sf#1 = 0#1 & n#1 <> 0#1) }> in
    <{
      if UNDEF then exn 0 else nop end;
      {DecodeBitMasks n imms immr 1 datasize};
      (* imm: temp[980] *)
      {arm_varid Xd} := X[Xn] | imm
    }>.

  (*logical imm*)
  Definition logical_imm :=
    let sf := n.[31] in
    let opc := n.[29,31] in
    let n_ := n.[22] in
    let Rd := n.[0,5] in
    let Rn := n.[5,10] in
    let imms := n.[10,16] in
    let immr := n.[16,22] in
    match[bits] sf, opc, n_ with
  | "0  -   1" => UDF (* Unallocated. *)
  | "0  00  0" => ARM_LOGICAL_IMM ARM_AND_IMM Rn Rd immr imms sf n_ (* AND (immediate) - 32-bit variant on page C6-775 *)
  | "0  01  0" => ARM_LOGICAL_IMM ARM_ORR_IMM Rn Rd immr imms sf n_ (* ORR (immediate) - 32-bit variant on page C6-1125 *)
  | "0  10  0" => ARM_LOGICAL_IMM ARM_EOR_IMM Rn Rd immr imms sf n_ (* EOR (immediate) - 32-bit variant on page C6-896 *)
  | "0  11  0" => ARM_LOGICAL_IMM ARM_ANDS_IMM Rn Rd immr imms sf n_ (* ANDS (immediate) - 32-bit variant on page C6-779 *)
  | "1  00  -" => ARM_LOGICAL_IMM ARM_AND_IMM Rn Rd immr imms sf n_ (* AND (immediate) - 64-bit variant on page C6-775 *)
  | "1  01  -" => ARM_LOGICAL_IMM ARM_ORR_IMM Rn Rd immr imms sf n_ (* ORR (immediate) - 64-bit variant on page C6-1125 *)
  | "1  10  -" => ARM_LOGICAL_IMM ARM_EOR_IMM Rn Rd immr imms sf n_ (* EOR (immediate) - 64-bit variant on page C6-896 *)
  | "1  11  -" => ARM_LOGICAL_IMM ARM_ANDS_IMM Rn Rd immr imms sf n_ (* ANDS (immediate) - 64-bit variant on page C6-779 *)
  else UDF end.

  Definition arm_movk_imm2il Xd imm16 size shift :=
    <{
      (* pos *) temp[100] := shift#64 << 4#64;
      (* Clip the shift to 16 if using 32-bit variant *)
      if (Xtemp[100] > 16#64) & (size#64=32#64) then temp[100] := 16#64 else nop end;
      (* mask *) (temp[101] := {Ones 64 (Word 16 64)} << Xtemp[100]);
      {arm_varid Xd} := X[Xd] & (! Xtemp[101]) | (imm16#64 << Xtemp[100])
    }>.

  Definition arm_movn_imm2il Xd imm16 size shift :=
    <{
      (* pos *) temp[100] := shift#64 << 4#64;
      (* Clip the shift to 16 if using 32-bit variant *)
      if (Xtemp[100] > 16#64) & (size#64=32#64) then temp[100] := 16#64 else nop end;
      (* mask *) (temp[101] := {Ones 64 (Word 16 64)} << Xtemp[100]);
      {arm_varid Xd} := ! (imm16#64 << Xtemp[100])
    }>.


  Definition arm_movz_imm2il Xd imm16 size shift :=
    <{
      (* pos *) temp[100] := shift#64 << 4#64;
      (* Clip the shift to 16 if using 32-bit variant *)
      if (Xtemp[100] > 16#64) & (size#64=32#64) then temp[100] := 16#64 else nop end;
      (* mask *) (temp[101] := {Ones 64 (Word 16 64)} << Xtemp[100]);
      {arm_varid Xd} := (imm16#64 << Xtemp[100])
    }>.


  Definition move_wide_imm :=
    let sf := n.[31] in
    let opc := n.[29,31] in
    let hw := n.[21,23] in
    let Rd := n.[0,5] in
    let imm16 := n.[5,21] in
    match[bits] sf, opc, hw with
    | "-  01  - " => UDF (* Unallocated. *)
    | "0  -   1x" => UDF (* Unallocated. *)
    | "0  00  - " => ARM_MOVE_IMM ARM_MOVN_IMM Rd imm16 32 hw (* MOVN - 32-bit variant on page C6-1100 *)
    | "0  10  - " => ARM_MOVE_IMM ARM_MOVZ_IMM Rd imm16 32 hw (* MOVZ - 32-bit variant on page C6-1102 *)
    | "0  11  - " => ARM_MOVE_IMM ARM_MOVK_IMM Rd imm16 32 hw (* MOVK - 32-bit variant on page C6-1098 *)
    | "1  00  - " => ARM_MOVE_IMM ARM_MOVN_IMM Rd imm16 64 hw (* MOVN - 64-bit variant on page C6-1100 *)
    | "1  10  - " => ARM_MOVE_IMM ARM_MOVZ_IMM Rd imm16 64 hw (* MOVZ - 64-bit variant on page C6-1102 *)
    | "1  11  - " => ARM_MOVE_IMM ARM_MOVK_IMM Rd imm16 64 hw (* MOVK - 64-bit variant on page C6-1098 *)
    else UDF end.

  (*  If <imms> is greater than or equal to <immr>, this copies a bitfield of (<imms>-<immr>+1) bits starting from bit position
      <immr> in the source register to the least significant bits of the destination register.

      If <imms> is less than <immr>, this copies a bitfield of (<imms>+1) bits from the least significant bits of the source
      register to bit position (regsize-<immr>) of the destination register, where regsize is the destination register size of 32
      or 64 bits.

      In both cases the destination bits below and above the bitfield are set to zero *)

  Definition arm_ubfm_imm2il (Xn Xd immr imms sf n:N) :=
    let bit32variant := <{sf#1 = 0#1 & n#1 = 0#1}> in
    let datasize := (if sf =? 1 then 64 else 32) in
    let wmask := <{Xtemp[980]}> in
    let tmask := <{Xtemp[990]}> in
    let UNDEF := <{ (sf#1 = 1#1 & n#1 <> 1#1) |
                    ((sf#1 = 0#1) & (n#1 <> 0#1 | (immr#6 [5] <> 0#1) | (imms#6[5] <> 0#1))) }> in
    <{
      if UNDEF then exn 0 else nop end;
      {DecodeBitMasks n imms immr 0 datasize};
      (* wmask: temp[980]; tmask: temp[990] *)
      (* src *) temp[1000] := X[Xn];
      (* bot *) temp[1001] := {ROR datasize <{Xtemp[1000]}> immr} & wmask;
      {arm_varid Xd} := Xtemp[1001] & tmask
    }>.

  Definition arm_bfm_imm2il (Xn Xd immr imms sf n:N) :=
    let bit32variant := <{sf#1 = 0#1 & n#1 = 0#1}> in
    let datasize := (if sf =? 1 then 64 else 32) in
    let wmask := <{Xtemp[980]}> in
    let tmask := <{Xtemp[990]}> in
    let dst := <{Xtemp[1000]}> in
    let bot := <{Xtemp[3000]}> in
    let UNDEF := <{ (sf#1 = 1#1 & n#1 <> 1#1) |
                    ((sf#1 = 0#1) & (n#1 <> 0#1 | (immr#6 [5] <> 0#1) | (imms#6[5] <> 0#1))) }> in
    <{
      if UNDEF then exn 0 else nop end;
      {DecodeBitMasks n imms immr 0 datasize};
      (* wmask: temp[980]; tmask: temp[990] *)
      (* dst *) temp[1000] := lcast datasize X[Xd];
      (* src *) temp[2000] := lcast datasize X[Xn];
      (* bot *) temp[3000] := (dst & !wmask) | ({ROR datasize <{Xtemp[2000]}> immr} & wmask);
      {arm_varid Xd} := ucast 64 ((dst * !tmask) | (bot & tmask))
    }>.

  Definition pilxbits (w:N) (n lo hi:exp) :=
    <{ (n >> lo) % (1#w << (hi-lo)) }>.

  Definition arm_sbfm_imm2il (Xn Xd immr imms sf n:N) :=
    let bit32variant := <{sf#1 = 0#1 & n#1 = 0#1}> in
    let datasize := (if sf =? 1 then 64 else 32) in
    let wmask := <{Xtemp[980]}> in
    let tmask := <{Xtemp[990]}> in
    let src := <{Xtemp[2000]}> in
    let bot := <{Xtemp[3000]}> in
    let top := <{Xtemp[4000]}> in
    let UNDEF := <{ (sf#1 = 1#1 & n#1 <> 1#1) |
                    ((sf#1 = 0#1) & (n#1 <> 0#1 | (immr#6 [5] <> 0#1) | (imms#6[5] <> 0#1))) }> in
    <{
      if UNDEF then exn 0 else nop end;
      {DecodeBitMasks n imms immr 0 datasize};
      (* wmask: temp[980]; tmask: temp[990] *)
      (* src *) temp[2000] := lcast datasize X[Xn];
      (* bot *) temp[3000] := {ROR datasize src immr} & wmask;
      (* top *) {Replicate 4000 4001 1 64 (pilxbits datasize src (Word 0 datasize) (Word 1 datasize))};
      {arm_varid Xd} := ucast 64 ((top & !tmask) | (bot & tmask))
    }>.

  Definition bitfield :=
    let sf := n.[31] in
    let opc := n.[29,31] in
    let n_ := n.[22] in
    let Rd := n.[0,5] in
    let Rn := n.[5,10] in
    let imms := n.[10,16] in
    let immr := n.[16,22] in
    match[bits] sf, opc, n_ with
    | "-  11  -" => UDF (* Unallocated. *)
    | "0  -   1" => UDF (* Unallocated. *)
    | "0  00  0" => ARM_LOGICAL_IMM ARM_SBFM_IMM Rn Rd immr imms sf n_ (* SBFM - 32-bit variant on page C6-1170 *)
    | "0  01  0" => ARM_LOGICAL_IMM ARM_BFM_IMM Rn Rd immr imms sf n_ (* BFM - 32-bit variant on page C6-804 *)
    | "0  10  0" => ARM_LOGICAL_IMM ARM_UBFM_IMM Rn Rd immr imms sf n_ (* UBFM - 32-bit variant on page C6-1351 *)
    | "1  -   0" => UDF (* Unallocated. *)
    | "1  00  1" => ARM_LOGICAL_IMM ARM_SBFM_IMM Rn Rd immr imms sf n_ (* SBFM - 64-bit variant on page C6-1170 *)
    | "1  01  1" => ARM_LOGICAL_IMM ARM_BFM_IMM Rn Rd immr imms sf n_ (* BFM - 64-bit variant on page C6-804 *)
    | "1  10  1" => ARM_LOGICAL_IMM ARM_UBFM_IMM Rn Rd immr imms sf n_ (* UBFM - 64-bit variant on page C6-1351 *)
    else UDF end.

  Definition extract :=
    let sf := n.[31] in
    let op21 := n.[29,31] in
    let n_ := n.[22] in
    let o0 := n.[21] in
    let imms := n.[10,16] in
    match[bits] sf, op21, n_, o0, imms with
    | "-  x1  -  -  -     " => UDF (* Unallocated. *)
    | "-  00  -  1  -     " => UDF (* Unallocated. *)
    | "-  1x  -  -  -     " => UDF (* Unallocated. *)
    | "0  -   -  -  1xxxxx" => UDF (* Unallocated. *)
    | "0  -   1  -  -     " => UDF (* Unallocated. *)
    | "0  00  0  0  0xxxxx" => ARM_EXTRACT (* EXTR - 32-bit variant on page C6-903 *)
    | "1  -   0  -  -     " => UDF (* Unallocated. *)
    | "1  00  1  0  -     " => ARM_EXTRACT (* EXTR - 64-bit variant on page C6-903 *)
    else UDF end.

  Definition dp_imm :=
    let op0:= n.[23,26] in
    match[bits] op0 with
  | "00x" => pc_rel (* PC-rel. addressing *)
  | "010" => add_sub_imm (* Add/subtract (immediate) *)
  (*| 011 => add_sub_imm_tags  Add/subtract (immediate, with tags) on page C4-254 *)
  | "100" => logical_imm (* Logical (immediate) on page C4-254 *)
  | "101" => move_wide_imm (* Move wide (immediate) on page C4-255 *)
  | "110" => bitfield (* Bitfield on page C4-256 *)
  | "111" => extract (* Extract on page C4-256 *)
   else UDF end.

  Definition arm_b_cond2il (cond imm19:N) :=
    let offset := <{scast 64 (imm19#19++0#2)}> in
      <{if {ConditionHolds cond}
      then jmp PC + offset else nop end}>.

  Definition cond_branch :=
    let o1 := n.[24] in
    let imm19 := n.[5,24] in
    let o0 := n.[4] in
    let cond := n.[0,4] in
    match[bits] o1, o0 with
    | "0  0" => ARM_B_COND cond imm19 (* B.cond *)
    | "0  1" => UDF (* Unallocated. *)
    | "1  -" => UDF (* Unallocated. *)
    else UDF end.

  Definition exc_gen :=
    let opc := n.[21,24] in
    let op2 := n.[2,5] in
    let LL := n.[0,2] in
    match[bits] opc, op2, LL with
    | "-    xx1  - " => UDF (* Unallocated. *)
    | "-    x1x  - " => UDF (* Unallocated. *)
    | "-    1xx  - " => UDF (* Unallocated. *)
    | "000  000  00" => UDF (* Unallocated. *)
    | "000  000  01" => ARM_SVC (* SVC *)
    | "000  000  10" => ARM_HVC (* HVC *)
    | "000  000  11" => ARM_SMC (* SMC *)
    | "001  000  x1" => UDF (* Unallocated. *)
    | "001  000  00" => ARM_BRK (* BRK *)
    | "001  000  1x" => UDF (* Unallocated. *)
    | "010  000  x1" => UDF (* Unallocated. *)
    | "010  000  00" => ARM_HLT (* HLT *)
    | "010  000  1x" => UDF (* Unallocated. *)
    | "011  000  01" => UDF (* Unallocated. *)
    | "011  000  1x" => UDF (* Unallocated. *)
    | "100  000  00" => UDF (* Unallocated. *)
    | "101  000  00" => UDF (* Unallocated. *)
    | "101  000  01" => ARM_DCPS1 (* DCPS1 *)
    | "101  000  10" => ARM_DCPS2 (* DCPS2 *)
    | "101  000  11" => ARM_DCPS3 (* DCPS3 *)
    | "110  000  - " => UDF (* Unallocated. *)
    | "111  000  01" => UDF (* Unallocated. *)
    | "111  000  1x" => UDF (* Unallocated. *)
    else UDF end.

  Definition arm_nop2il := <{nop}>.
  Definition arm_yield2il := <{nop}>.
  Definition arm_wfe2il := <{nop}>.
  Definition arm_wfi2il := <{nop}>.
  Definition arm_sev2il := <{nop}>.
  Definition arm_sevl2il := <{nop}>.
  Definition arm_esb2il := <{nop}>.
  Definition arm_psb_csync2il := <{nop}>.
  Definition arm_tsb_csync2il := <{nop}>.
  Definition arm_csdb2il := <{nop}>.
  Definition arm_bti2il := <{nop}>.

  Definition hints :=
    let CRm := n.[8,12] in
    let op2 := n.[5,8] in
    match[bits] CRm, op2 with
    | "-     -  " => ARM_HINT (* HINT - *)
    | "0000  000" => ARM_NOP (* NOP - *)
    | "0000  001" => ARM_YIELD (* YIELD - *)
    | "0000  010" => ARM_WFE (* WFE - *)
    | "0000  011" => ARM_WFI (* WFI - *)
    | "0000  100" => ARM_SEV (* SEV - *)
    | "0000  101" => ARM_SEVL (* SEVL - *)
    | "0000  111" => ARM_XPACD (* XPACD, XPACI, XPACLRI Armv8.3 *)
    | "0001  000" => ARM_PACIA (* PACIA, PACIA1716, PACIASP, PACIAZ, PACIZA - PACIA1716 variant on page C6-1133 Armv8.3 *)
    | "0001  010" => ARM_PACIB (* PACIB, PACIB1716, PACIBSP, PACIBZ, PACIZB - PACIB1716 variant on page C6-1135 Armv8.3 *)
    | "0001  100" => ARM_AUTIA (* AUTIA, AUTIA1716, AUTIASP, AUTIAZ, AUTIZA - AUTIA1716 variant on page C6-794 Armv8.3 *)
    | "0001  110" => ARM_AUTIB (* AUTIB, AUTIB1716, AUTIBSP, AUTIBZ, AUTIZB - AUTIB1716 variant on page C6-796 Armv8.3 *)
    | "0010  000" => ARM_ESB (* ESB Armv8.2 *)
    | "0010  001" => ARM_PSB_CSYNC (* PSB_CSYNC Armv8.2 *)
    | "0010  010" => ARM_TSB_CSYNC (* TSB_CSYNC Armv8.4 *)
    | "0010  100" => ARM_CSDB (* CSDB - *)
    | "0011  000" => ARM_PACIA (* PACIA, PACIA1716, PACIASP, PACIAZ, PACIZA - PACIAZ variant on page C6-1133 Armv8.3 *)
    | "0011  001" => ARM_PACIA (* PACIA, PACIA1716, PACIASP, PACIAZ, PACIZA - PACIASP variant on page C6-1133 Armv8.3 *)
    | "0011  010" => ARM_PACIB (* PACIB, PACIB1716, PACIBSP, PACIBZ, PACIZB - PACIBZ variant on page C6-1135 Armv8.3 *)
    | "0011  011" => ARM_PACIB (* PACIB, PACIB1716, PACIBSP, PACIBZ, PACIZB - PACIBSP variant on page C6-1135 Armv8.3 *)
    | "0011  100" => ARM_AUTIA (* AUTIA, AUTIA1716, AUTIASP, AUTIAZ, AUTIZA - AUTIAZ variant on page C6-794 Armv8.3 *)
    | "0011  101" => ARM_AUTIA (* AUTIA, AUTIA1716, AUTIASP, AUTIAZ, AUTIZA - AUTIASP variant on page C6-794 Armv8.3 *)
    | "0011  110" => ARM_AUTIB (* AUTIB, AUTIB1716, AUTIBSP, AUTIBZ, AUTIZB - AUTIBZ variant on page C6-796 Armv8.3 *)
    | "0011  111" => ARM_AUTIB (* AUTIB, AUTIB1716, AUTIBSP, AUTIBZ, AUTIZB - AUTIBSP variant on page C6-796 Armv8.3 *)
    | "0100  xx0" => ARM_BTI (* BTI Armv8.5 *)
    else UDF end.

  Definition arm_clrex2il := Nop.
  Definition arm_dmb2il := Nop.
  Definition arm_isb2il := Nop.
  Definition arm_sb2il := Nop.
  Definition arm_dsb2il := Nop.
  Definition arm_ssbb2il := Nop.
  Definition arm_pssbb2il := Nop.

  Definition barriers :=
    let CRm := n.[8,12] in
    let op2 := n.[5,8] in
    let rt := n.[0,5] in
    match[bits] CRm, op2, rt with
    | "-       000  -      " => UDF (* Unallocated. *)
    | "-       001  -      " => UDF (* Unallocated. *)
    | "-       010  11111  " => ARM_CLREX (* CLREX *)
    | "-       101  11111  " => ARM_DMB (* DMB *)
    | "-       110  11111  " => ARM_ISB (* ISB *)
    | "-       111  !=11111" => UDF (* Unallocated. *)
    | "-       111  11111  " => ARM_SB (* SB *)
    | "!=0x00  100  11111  " => ARM_DSB (* DSB *)
    | "0000    100  11111  " => ARM_SSBB (* SSBB *)
    | "0001    011  -      " => UDF (* Unallocated. *)
    | "001x    011  -      " => UDF (* Unallocated. *)
    | "01xx    011  -      " => UDF (* Unallocated. *)
    | "0100    100  11111  " => ARM_PSSBB (* PSSBB *)
    | "1xxx    011  -      " => UDF (* Unallocated. *)
    else UDF end.

  (* We do not model the system registers/bits that MSR writes to. *)
  Definition arm_msr_imm2il := Nop.
  Definition arm_cfinv2il := Move R_CY (UnOp OP_NOT (Var R_CY)).

  (* XAFLAG and AXFLAG convert to/from flag format to an alternative representation
     used by some floating point software.  We do not support floating points, but
     we can support these instructions so we might as well.
     If we do not want to model the FlagFormatExt then set this to undefined behavior. *)
  Definition arm_xaflag2il :=
    <{
      (*N*) temp[1] := ucast 8 (!C & !Z);
      (*Z*) temp[2] := ucast 8 ( C &  Z);
      (*C*) temp[3] := ucast 8 ( C |  Z);
      (*V*) temp[4] := ucast 8 (!C &  Z);
      R_NG := Xtemp[1];
      R_ZR := Xtemp[2];
      R_CY := Xtemp[3];
      R_OV := Xtemp[4]
    }>.
  Definition arm_axflag2il :=
    <{
      (*Z*) temp[2] :=  ucast 8 (Z |  V);
      (*C*) temp[3] :=  ucast 8 (C & !V);
      R_NG := 0#8;
      R_ZR := Xtemp[2];
      R_CY := Xtemp[3];
      R_OV := 0#8
    }>.

  Definition pstate :=
    let op1 := n.[16,19] in
    let op2 := n.[5,8] in
    let rt := n.[0,5] in
    match[bits] op1, op2, rt with
    | "-    -    !=11111" => UDF (* Unallocated. - *)
    | "-    -    11111  " => ARM_MSR_IMM (* MSR (immediate) - *)
    | "000  000  11111  " => ARM_CFINV (* CFINV Armv8.4 *)
    | "000  001  11111  " => ARM_XAFLAG (* XAFLAG Armv8.5 *)
    | "000  010  11111  " => ARM_AXFLAG (* AXFLAG Armv8.5 *)
    else UDF end.

  (* The system instructions are out of scope. We treat them as undefined
     although only a subset of the encodings are undefined.
     See C5-366 for more information. *)
  Definition arm_sys2il := havoc.
  Definition arm_sysl2il := havoc.

  Definition sys_inst :=
    let L := n.[21] in
    match[bits] L with
    | "0" => ARM_SYS (* SYS *)
    | "1" => ARM_SYSL (* SYSL *)
    else UDF end.

  (* The auxiliary function is undefined:
     // Read from a system register and return the contents of the register.
     bits(64) AArch64.SysRegRead(integer op0, integer op1, integer crn, integer crm, integer op2); *)
  Definition arm_msr_reg2il := havoc.
  (* The auxiliary function is undefined:
     // Read from a system register and return the contents of the register.
     bits(64) AArch64.SysRegRead(integer op0, integer op1, integer crn, integer crm, integer op2); *)
  Definition arm_mrs2il := havoc.

  Definition sys_reg_move :=
    let L := n.[21] in
    match[bits] L with
    | "0" => ARM_MSR_REG (* MSR (register) *)
    | "1" => ARM_MRS (* MRS *)
    else UDF end.


  (* Undefined behavior when PCA extension is unsupported. *)
  Definition arm_braaz2il (Xn:N) := havoc.
  Definition arm_blraaz2il (Xn:N) := havoc.
  Definition arm_retaa2il := havoc.
  Definition arm_blraa_reg2il := havoc.
  Definition arm_braa_reg2il := havoc.

  (* Undefined behavior in EL0 *)
  Definition arm_eret2il := havoc.
  Definition arm_eretaa2il := havoc.
  Definition arm_drps2il := havoc.

  Definition arm_br2il Xn := <{branch X[Xn]}>.
  Definition arm_blr2il Xn := <{temp[1]:=X[Xn]; var[30] := PC+4#64; branch Xtemp[1]}>.
  Definition arm_ret2il Xn := <{branch X[Xn]}>.

  Definition uncond_b_reg :=
    let opc := n.[21,25] in
    let op2 := n.[16,21] in
    let op3 := n.[10,16] in
    let Rn := n.[5,10] in
    let op4 := n.[0,5] in
    match[bits] opc, op2, op3, Rn, op4 with
  | "-     !=11111  -         -        -      " => UDF (* Unallocated. - *)
  | "0000  11111    000000    -        !=00000" => UDF (* Unallocated. - *)
  | "0000  11111    000000    -        00000  " => ARM_BR Rn (* BR - *)
  | "0000  11111    000001    -        -      " => UDF (* Unallocated. - *)
  | "0000  11111    000010    -        !=11111" => UDF (* Unallocated. - *)
  | "0000  11111    000010    -        11111  " => ARM_BRAAZ Rn (* BRAA, BRAAZ, BRAB, BRABZ - Key A, zero modifier variant on page C6-817 Armv8.3 *)
  | "0000  11111    000011    -        !=11111" => UDF (* Unallocated. - *)
  | "0000  11111    000011    -        11111  " => ARM_BRAAZ Rn (* BRAA, BRAAZ, BRAB, BRABZ - Key B, zero modifier variant on page C6-817 Armv8.3 *)
  | "0000  11111    0001xx    -        -      " => UDF (* Unallocated. - *)
  | "0000  11111    001xxx    -        -      " => UDF (* Unallocated. - *)
  | "0000  11111    01xxxx    -        -      " => UDF (* Unallocated. - *)
  | "0000  11111    1xxxxx    -        -      " => UDF (* Unallocated. - *)
  | "0001  11111    000000    -        !=00000" => UDF (* Unallocated. - *)
  | "0001  11111    000000    -        00000  " => ARM_BLR Rn (* BLR - *)
  | "0001  11111    000001    -        -      " => UDF (* Unallocated. - *)
  | "0001  11111    000010    -        !=11111" => UDF (* Unallocated. - *)
  | "0001  11111    000010    -        11111  " => ARM_BLRAAZ (* BLRAA, BLRAAZ, BLRAB, BLRABZ - Key A, zero modifier variant on page C6-814 Armv8.3 *)
  | "0001  11111    000011    -        !=11111" => UDF (* Unallocated. - *)
  | "0001  11111    000011    -        11111  " => ARM_BLRAAZ (* BLRAA, BLRAAZ, BLRAB, BLRABZ - Key B, zero modifier variant on page C6-814 Armv8.3 *)
  | "0001  11111    0001xx    -        -      " => UDF (* Unallocated. - *)
  | "0001  11111    001xxx    -        -      " => UDF (* Unallocated. - *)
  | "0001  11111    01xxxx    -        -      " => UDF (* Unallocated. - *)
  | "0001  11111    1xxxxx    -        -      " => UDF (* Unallocated. - *)
  | "0010  11111    000000    -        !=00000" => UDF (* Unallocated. -       *)
  | "0010  11111    000000    -        00000  " => ARM_RET Rn (* RET - *)
  | "0010  11111    000001    -        -      " => UDF (* Unallocated. - *)
  | "0010  11111    000010    !=11111  !=11111" => UDF (* Unallocated. - *)
  | "0010  11111    000010    11111    11111  " => ARM_RETAA (* RETAA, RETAB - RETAA variant on page C6-1148 Armv8.3 *)
  | "0010  11111    000011    !=11111  !=11111" => UDF (* Unallocated. - *)
  | "0010  11111    000011    11111    11111  " => ARM_RETAA (* RETAA, RETAB - RETAB variant on page C6-1148 Armv8.3 *)
  | "0010  11111    0001xx    -        -      " => UDF (* Unallocated. - *)
  | "0010  11111    001xxx    -        -      " => UDF (* Unallocated. - *)
  | "0010  11111    01xxxx    -        -      " => UDF (* Unallocated. - *)
  | "0010  11111    1xxxxx    -        -      " => UDF (* Unallocated. - *)
  | "0011  11111    -         -        -      " => UDF (* Unallocated. - *)
  | "0100  11111    000000    !=11111  !=00000" => UDF (* Unallocated. - *)
  | "0100  11111    000000    !=11111  00000  " => UDF (* Unallocated. - *)
  | "0100  11111    000000    11111    !=00000" => UDF (* Unallocated. - *)
  | "0100  11111    000000    11111    00000  " => ARM_ERET (* ERET - *)
  | "0100  11111    000001    -        -      " => UDF (* Unallocated. - *)
  | "0100  11111    000010    !=11111  !=11111" => UDF (* Unallocated. - *)
  | "0100  11111    000010    !=11111  11111  " => UDF (* Unallocated. - *)
  | "0100  11111    000010    11111    !=11111" => UDF (* Unallocated. - *)
  | "0100  11111    000010    11111    11111  " => ARM_ERETAA (* ERETAA, ERETAB - ERETAA variant on page C6-901 Armv8.3 *)
  | "0100  11111    000011    !=11111  !=11111" => UDF (* Unallocated. - *)
  | "0100  11111    000011    !=11111  11111  " => UDF (* Unallocated. - *)
  | "0100  11111    000011    11111    !=11111" => UDF (* Unallocated. - *)
  | "0100  11111    000011    11111    11111  " => ARM_ERETAA (* ERETAA, ERETAB - ERETAB variant on page C6-901 Armv8.3 *)
  | "0100  11111    0001xx    -        -      " => UDF (* Unallocated. - *)
  | "0100  11111    001xxx    -        -      " => UDF (* Unallocated. - *)
  | "0100  11111    01xxxx    -        -      " => UDF (* Unallocated. - *)
  | "0100  11111    1xxxxx    -        -      " => UDF (* Unallocated. - *)
  | "0101  11111    !=000000  -        -      " => UDF (* Unallocated. - *)
  | "0101  11111    000000    !=11111  !=00000" => UDF (* Unallocated. - *)
  | "0101  11111    000000    !=11111  00000  " => UDF (* Unallocated. - *)
  | "0101  11111    000000    11111    !=00000" => UDF (* Unallocated. - *)
  | "0101  11111    000000    11111    00000  " => ARM_DRPS (* DRPS - *)
  | "011x  11111    -         -        -      " => UDF (* Unallocated. - *)
  | "1000  11111    00000x    -        -      " => UDF (* Unallocated. - *)
  | "1000  11111    000010    -        -      " => ARM_BRAA_REG (* BRAA, BRAAZ, BRAB, BRABZ - Key A, register modifier variant on page C6-817 Armv8.3 *)
  | "1000  11111    000011    -        -      " => ARM_BRAA_REG (* BRAA, BRAAZ, BRAB, BRABZ - Key B, register modifier variant on page C6-817 Armv8.3 *)
  | "1000  11111    0001xx    -        -      " => UDF (* Unallocated. - *)
  | "1000  11111    001xxx    -        -      " => UDF (* Unallocated. - *)
  | "1000  11111    01xxxx    -        -      " => UDF (* Unallocated. - *)
  | "1000  11111    1xxxxx    -        -      " => UDF (* Unallocated. - *)
  | "1001  11111    00000x    -        -      " => UDF (* Unallocated. - *)
  | "1001  11111    000010    -        -      " => ARM_BLRAA_REG (* BLRAA, BLRAAZ, BLRAB, BLRABZ - Key A, register modifier variant on page C6-814 Armv8.3 *)
  | "1001  11111    000011    -        -      " => ARM_BLRAA_REG (* BLRAA, BLRAAZ, BLRAB, BLRABZ - Key B, register modifier variant on page C6-814 Armv8.3 *)
  | "1001  11111    0001xx    -        -      " => UDF (* Unallocated. - *)
  | "1001  11111    001xxx    -        -      " => UDF (* Unallocated. - *)
  | "1001  11111    01xxxx    -        -      " => UDF (* Unallocated. - *)
  | "1001  11111    1xxxxx    -        -      " => UDF (* Unallocated. - *)
  | "101x  11111    -         -        -      " => UDF (* Unallocated. - *)
  | "11xx  11111    -         -        -      " => UDF (* Unallocated. - *)
  else UDF end.

  Definition arm_b2il imm26 :=
    let offset := <{scast 64 (imm26#28 << 2#28)}> in
    <{jmp PC+offset}>.

  Definition arm_bl2il imm26 :=
    let offset := <{scast 64 (imm26#28 << 2#28)}> in
    <{{arm_varid 30} := PC + 4#64; jmp PC+offset}>.

  Definition uncond_b_imm :=
    let op := n.[31] in
    let imm26 := n.[0,26] in
    match[bits] op with
    | "0" => ARM_B  imm26 (* B *)
    | "1" => ARM_BL imm26 (* BL *)
    else UDF end.

  Definition arm_cbz2il Xn imm19 size :=
    let offset := <{scast 64 (imm19#21 << 2#21)}> in
    let target := <{PC + offset}> in <{
    if lcast size X[Xn] = 0#size then {BranchTo size target} else nop end
  }>.

  Definition arm_cbnz2il Xn imm19 size :=
    let offset := <{scast 64 (imm19#21 << 2#21)}> in
    let target := <{PC + offset}> in <{
    if !(lcast size X[Xn] = 0#size) then {BranchTo size target} else nop end
  }>.

  Definition comp_and_b :=
    let sf := n.[31] in
    let op := n.[24] in
    let Rt := n.[0,5] in
    let imm19 := n.[5,24] in
    match[bits] sf, op with
    | "0  0" => ARM_CBZ Rt imm19 32 (* CBZ - 32-bit variant *)
    | "0  1" => ARM_CBNZ Rt imm19 32 (* CBNZ - 32-bit variant *)
    | "1  0" => ARM_CBZ Rt imm19 64 (* CBZ - 64-bit variant *)
    | "1  1" => ARM_CBNZ Rt imm19 64 (* CBNZ - 64-bit variant *)
    else UDF end.



  (* C6-1341 *)
  (* Here the position is calculated in Gallina because the Extract expression
     takes Gallina Ns for the indices, not exps. *)
  Definition arm_tbz2il (Xt imm14 b5 b40:N) :=
    let pos := cbits b5 5 b40 in
    let offset := <{ scast 64 (imm14#16 << 2#16) }> in <{
      if  X[Xt][pos] = 0#1 then branch (PC + offset) else nop end
  }>.

  (* C6-1340 *)
  Definition arm_tbnz2il (Xt imm14 b5 b40:N) :=
    let pos := cbits b5 5 b40 in
    let offset := <{ scast 64 (imm14#16 << 2#16) }> in <{
      if  X[Xt][pos] = 1#1 then branch (PC + offset) else nop end
  }>.


  Definition test_and_b :=
    let op := n.[24] in
    let b5 := n.[31] in
    let b40 := n.[19,24] in
    let imm14 := n.[5,19] in
    let Rt := n.[0,5] in
    match[bits] op with
    | "0" => ARM_TBZ Rt imm14 b5 b40(* TBZ *)
    | "1" => ARM_TBNZ Rt imm14 b5 b40 (* TBNZ *)
    else UDF end.

  Definition branch_exc :=
    let op0 := n.[29,32] in
    let op1 := n.[12,26] in
    let op2 := n.[0,5] in
    match[bits] op0, op1, op2 with
    | "010  0xxxxxxxxxxxxx  -    " => cond_branch (* Conditional branch (immediate) *)
    | "110  00xxxxxxxxxxxx  -    " => exc_gen (* Exception generation on page C4-258 *)
    | "110  01000000110010  11111" => hints (* Hints on page C4-258 *)
    | "110  01000000110011  -    " => barriers (* Barriers on page C4-260 *)
    | "110  0100000xxx0100  -    " => pstate (* PSTATE on page C4-260 *)
    | "110  0100x01xxxxxxx  -    " => sys_inst (* System instructions on page C4-261 *)
    | "110  0100x1xxxxxxxx  -    " => sys_reg_move (* System register move on page C4-261 *)
    | "110  1xxxxxxxxxxxxx  -    " => uncond_b_reg (* Unconditional branch (register) on page C4-262 *)
    | "x00  -               -    " => uncond_b_imm (* Unconditional branch (immediate) on page C4-264 *)
    | "x01  0xxxxxxxxxxxxx  -    " => comp_and_b (* Compare and branch (immediate) on page C4-265 *)
    | "x01  1xxxxxxxxxxxxx  -    " => test_and_b (* Test and branch (immediate) on page C4-265 *)
    else UDF end.


  (* We do not model tag memory, this is a no-op if the SP is aligned. *)
  Definition arm_stg2il (Rn Rt imm9:N) (writeback postindex:bool) :=
    let offset := <{scast 64 (imm9 # 9) << (LOG2_TAG_GRANULE # 64) }> in
    let Xn := <{Rn # 64}> in
    let Xt := <{Rt # 64}> in <{
      (* V_TEMP 1000 := address
        V_TEMP 2000 := data *)
      if (Rn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Rn];
      if ! {b2exp postindex} then temp[1000] := Xtemp[1000] + offset else nop end;
      temp[2000] := X[Rt];
      temp[3000] := AllocTag Xtemp[2000]
    }>.

  (* Store Tag and Zero Multiple C6.2.306-1307
     This instruction's semantics are undefined for EL0. *)
  Definition arm_stzgm2il (t n:N) := havoc.

  (* Load Allocation Tag C6.2.122-962 *)
  Definition arm_ldg2il (Xn Xt imm9:N) :=
    let offset := <{scast 64 (imm9 # 9) << (LOG2_TAG_GRANULE # 64) }> in
    <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      temp[1000] := Xtemp[1000] + offset;
      temp[1000] := Align[Xtemp[1000],64,16];
      (* Skip tag access *)
      {arm_varid Xt} := Xtemp[1000]
  }>.

  (* Load Allocation Tag C6.2.122-962 *)
  Definition arm_stzg2il (Xn Xt imm9:N) (writeback postindex:bool) :=
    let offset := <{scast 64 (imm9 # 9) << (LOG2_TAG_GRANULE # 64) }> in
    <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      if !{b2exp postindex} then temp[1000] := Xtemp[1000] + offset else nop end;
      store[Xtemp[1000], 0 # 128, LittleE, 16];
      temp[2000] := X[Xt];
      temp[2001] := AllocTag (Xtemp[2000]);
      if {b2exp writeback} then
        if {b2exp postindex} then temp[1000] := Xtemp[1000] + offset else nop end;
        {arm_varid Xn} := Xtemp[1000]
      else
        nop
      end
  }>.

  (* Store Allocation Tags C6-1187 *)
  Definition arm_st2g2il (Xn Xt imm9:N) (writeback postindex:bool) :=
    let offset := <{scast 64 (imm9 # 9) << (LOG2_TAG_GRANULE # 64) }> in <{
      temp[2000] := X[Xt];
      temp[2001] := AllocTag (Xtemp[2000]);
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      if !{b2exp postindex} then temp[1000] := Xtemp[1000] + offset else nop end;
      if {b2exp writeback} then
        if {b2exp postindex} then temp[1000] := Xtemp[1000] + offset else nop end;
        {arm_varid Xn} := Xtemp[1000]
      else
        nop
      end
    }>.

  Definition arm_stgm2il (Xn Xt:N) := havoc.

  Definition arm_stz2g2il (Xn Xt imm9:N) (writeback postindex:bool) :=
    let offset := <{scast 64 (imm9 # 9) << (LOG2_TAG_GRANULE # 64) }> in <{
      temp[2000] := X[Xt];
      temp[2001] := AllocTag (Xtemp[2000]);
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      if !{b2exp postindex} then temp[1000] := Xtemp[1000] + offset else nop end;
      store[Xtemp[1000], (0#256), LittleE, 32];
      if {b2exp writeback} then
        if {b2exp postindex} then temp[1000] := Xtemp[1000] + offset else nop end;
        {arm_varid Xn} := Xtemp[1000]
      else
        nop
      end
    }>.

  Definition arm_ldgm2il (Xn Xt:N) := havoc.


    (*Loads and Stores C4.1.4-266*)
  Definition load_store_mem_tags :=
    let opc := n.[22,24] in
    let imm9 := n.[12,21] in
    let op2 := n.[10,12] in
    let Rn := n.[5,10] in
    let Rt := n.[0,5] in
    match[bits] opc, imm9, op2 with
      (* STG C4-276, C6-1207 *)
    | "00  -            01" => ARM_STG Rn Rt imm9 true  true  (* STG - Post-index variant on page C6-1207 Armv8.5 *)
    | "00  -            10" => ARM_STG Rn Rt imm9 false false (* STG - Signed offset variant on page C6-1207 Armv8.5 *)
    | "00  -            11" => ARM_STG Rn Rt imm9 true  false (* STG - Pre-index variant on page C6-1207 Armv8.5 *)
    | "00  000000000    00" => ARM_STZGM Rn Rt (* STZGM Armv8.5 *)
    | "01  -            00" => ARM_LDG Rn Rt imm9(* LDG Armv8.5 *)
    | "01  -            01" => ARM_STZG Rn Rt imm9 true  true  (* STZG - Post-index variant on page C6-1305 Armv8.5 *)
    | "01  -            10" => ARM_STZG Rn Rt imm9 false false (* STZG - Signed offset variant on page C6-1305 Armv8.5 *)
    | "01  -            11" => ARM_STZG Rn Rt imm9 true  false (* STZG - Pre-index variant on page C6-1305 Armv8.5 *)
    | "10  -            01" => ARM_ST2G Rn Rt imm9 true  true (* ST2G - Post-index variant on page C6-1187 Armv8.5 *)
    | "10  -            10" => ARM_ST2G Rn Rt imm9 false false (* ST2G - Signed offset variant on page C6-1187 Armv8.5 *)
    | "10  -            11" => ARM_ST2G Rn Rt imm9 true  false (* ST2G - Pre-index variant on page C6-1187 Armv8.5 *)
    | "10  !=000000000  00" => UDF (* Unallocated. - *)
    | "10  000000000    00" => ARM_STGM Rn Rt (* STGM Armv8.5 *)
    | "11  -            01" => ARM_STZ2G Rn Rt imm9 true  true (* STZ2G - Post-index variant on page C6-1303 Armv8.5 *)
    | "11  -            10" => ARM_STZ2G Rn Rt imm9 false false (* STZ2G - Signed offset variant on page C6-1303 Armv8.5 *)
    | "11  -            11" => ARM_STZ2G Rn Rt imm9 true  false (* STZ2G - Pre-index variant on page C6-1303 Armv8.5 *)
    | "11  !=000000000  00" => UDF (* Unallocated. - *)
    | "11  000000000    00" => ARM_LDGM Rn Rt(* LDGM Armv8.5 *)
    else UDF end.

  (* J1-7343
    // Compares the value stored at the passed-in memory address against the passed-in expected
    // value. If the comparison is successful, the value at the passed-in memory address is swapped
    // with the passed-in new_value.

    bits(w) MemAtomicCompareAndSwap(bits(64) addr, bits(w) expectedvalue,
        bits(w) newvalue, AccType ldacctype, AccType stacctype)*)
  Definition MemAtomicCampareAndSwap (w t:N) addr expectedvalue newvalue :=
    let bytes := N.shiftr w 3 in <{
      (* oldvalue *) temp[t] := ite BigEndian load[addr,BigE,bytes] load[addr,LittleE,bytes];
      if Xtemp[t] = expectedvalue then
        if BigEndian then store[addr,newvalue,BigE,bytes] else store[addr,newvalue,LittleE,bytes] end else nop end
    }>.

  Definition arm_casp2il (Xn Xs Xt size:N) :=
    let undefined := <{!HaveAtomicExt | Xs#5[0] = 1#1 | Xt#5[0] = 1#1}> in <{
      if undefined then havoc else
      (* comparevalue *) temp[1000] := ite BigEndian (lcast size X[Xn] ++ lcast size X[{N.succ Xn}])
                                                     (lcast size X[{N.succ Xn}] ++ lcast size X[Xn]);
      (* newvalue *) temp[2000] := ite BigEndian (lcast size X[Xt] ++ lcast size X[{N.succ Xt}])
                                                 (lcast size X[{N.succ Xt}] ++ lcast size X[Xt]);
      (* address temp[333] *) if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[333] := X[Xn];
      {MemAtomicCampareAndSwap (N.shiftl size 2) 334 <{Xtemp[333]}> <{Xtemp[1000]}> <{Xtemp[2000]}>};
      if BigEndian then
        var[Xs] := ucast 64 (Xtemp[334][{2*size-1}:size]);
        var[{N.succ Xs}] := ucast 64 (Xtemp[334][size:0])
      else
        var[Xs] := ucast 64 (Xtemp[334][size:0]);
        var[{N.succ Xs}] := ucast 64 (Xtemp[334][{2*size-1}:size])
      end
      end
    }>.

  Definition arm_casb2il (Xn Xs Xt:N) :=
    let undefined := <{!HaveAtomicExt}> in
    let comparevalue := <{lcast 8 X[Xs]}> in
    let newvalue := <{lcast 8 X[Xt]}> in <{
      if undefined then havoc else
      (* address temp[333] *) if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[333] := X[Xn];
      {MemAtomicCampareAndSwap 8 334 <{Xtemp[333]}> comparevalue newvalue};
      var[Xs] := ucast 64 Xtemp[334]
      end
    }>.

  Definition arm_cash2il (Xn Xs Xt:N) :=
    let undefined := <{!HaveAtomicExt}> in
    let comparevalue := <{lcast 16 X[Xs]}> in
    let newvalue := <{lcast 16 X[Xt]}> in <{
      if undefined then havoc else
      (* address temp[333] *) if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[333] := X[Xn];
      {MemAtomicCampareAndSwap 16 334 <{Xtemp[333]}> comparevalue newvalue};
      var[Xs] := ucast 64 Xtemp[334]
      end
    }>.

  Definition arm_cas2il (Xn Xs Xt size:N) :=
    let undefined := <{!HaveAtomicExt}> in
    let comparevalue := <{lcast size X[Xs]}> in
    let newvalue := <{lcast size X[Xt]}> in <{
      if undefined then havoc else
      (* address temp[333] *) if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[333] := X[Xn];
      {MemAtomicCampareAndSwap 32 334 <{Xtemp[333]}> comparevalue newvalue};
      var[Xs] := ucast 64 Xtemp[334]
      end
    }>.

  (* Exclusive operations are Nops when the PE does not have exclusive access
     to memory.  We model this by using an unknown value, thus necessitating
     exploring both possible branches during symbolic execution.

      We use exp to effect the unknown behavior to let the symbolic executor handle
     the case analysis instead of duplicating code paths. *)
  Definition arm_stxr2il_constr (size Xn Xs Xt:N) (rtunknown rnunknown:exp) :=
    let bytes := N.shiftr size 3 in
    <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end;
      temp[1000] := ite rnunknown X[Xn] (unknown 64);
      temp[2000] := ite rtunknown (lcast size X[Xt]) (unknown size);
      if unknown 1 then
        (* Store not attempted, returns error bit. *)
        var[Xs] := 1#64
      else
        if unknown 1 then
          (* Store succeeded, but returned status may still indicate failure *)
          store[Xtemp[1000],Xtemp[2000],bytes];
          var[Xs] := ucast 64 (unknown 1)
        else
          (* Store attempted but failed. *)
          var[Xs] := 0#64
        end
      end
    }>.

  Definition arm_stxr2il_size (size Xn Xs Xt:N) :=
    let constraint1 := <{Xs#5 = Xt#5}> in
    let constraint2 := <{Xs#5 = Xn#5 & Xn#5 <> 31#5}> in <{
      if ! constraint1 & ! constraint2 then {arm_stxr2il_constr size Xn Xs Xt (Word 0 1) (Word 0 1)} else
      if constraint1 then
        if unknown 1 then
          (* Constraint_UNDEFINED *) havoc
        else if unknown 1 then
          (* Constraint_NOP *) nop
        else (* Constraint_UNKNOWN or Constraint_NONE *)
        if constraint2 then
          (* Reached Constraint_UNDEFINED and Constraint_NOP above, so don't need to repeat *)
          {arm_stxr2il_constr size Xn Xs Xt (Unknown 1) (Unknown 1)}
        else
          {arm_stxr2il_constr size Xn Xs Xt (Unknown 1) (Word 0 1)}
        end (* End of constraint1 + constraint2 *)
      end end else
      (* !constraint1 + constraint2 *)
        if unknown 1 then
          (* Constraint_UNDEFINED *) havoc
        else if unknown 1 then
          (* Constraint_NOP *) nop
        else (* Constraint_UNKNOWN or Constraint_NONE *)
          {arm_stxr2il_constr size Xn Xs Xt (Word 0 1) (Unknown 1)}
        end end end end}>.

    Definition arm_stxrb2il := arm_stxr2il_size 8.
    Definition arm_stxrh2il := arm_stxr2il_size 16.
    Definition arm_stxr2il := arm_stxr2il_size.

    Definition arm_stlxrb2il := arm_stxr2il_size 8.
    Definition arm_stlxrh2il := arm_stxr2il_size 16.
    Definition arm_stlxr2il := arm_stxr2il_size.

    Definition arm_stllr2il_size (size Xn Xt:N) :=
      let bytes := N.shiftr size 3 in
      <{ if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end;
         store[X[Xn],(ucast 64 (lcast size X[Xt])),bytes]
      }>.

    Definition arm_stllrb2il := arm_stllr2il_size 8.
    Definition arm_stllrh2il := arm_stllr2il_size 16.
    Definition arm_stllr2il := arm_stllr2il_size.

    Definition arm_stlrb2il := arm_stllr2il_size 8.
    Definition arm_stlrh2il := arm_stllr2il_size 16.
    Definition arm_stlr2il := arm_stllr2il_size.

  (* TODO: Documentation say the address must be aligned on an element-size boundary,
     but the operation pseudocode does not seem to have it. I did not implement
     it on the first pass. Decide whether or not to add it. *)
  Definition arm_stxp2il_constr (size Xn Xs Xt Xt2:N) (rtunknown rnunknown:exp) :=
    let bytes := N.shiftr size 2 in
    let el1 := <{Xtemp[2000]}> in
    let el2 := <{Xtemp[3000]}> in
    <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end;
      (* address *) temp[1000] := ite rnunknown X[Xn] (unknown 64);
      (* element1 *) temp[2000] := lcast size X[Xt];
      (* element2 *) temp[3000] := lcast size X[Xt2];
      if rtunknown then temp[2000] := unknown size; temp[3000] := unknown size else nop end;
      (* data *) temp[4000] := ite BigEndian (el1++el2) (el2++el1);
      if unknown 1 then
        (* Store not attempted, returns error bit. *)
        var[Xs] := 1#64
      else
        if unknown 1 then
          (* Store succeeded, but returned status may still indicate failure *)
          store[Xtemp[1000],Xtemp[4000],bytes];
          var[Xs] := ucast 64 (unknown 1)
        else
          (* Store attempted but failed. *)
          var[Xs] := 0#64
        end
      end
    }>.

  Definition arm_stxp2il_size (size Xn Xs Xt Xt2:N) :=
    let constraint1 := <{Xs#5 = Xt#5 | Xs#5 = Xt2#5}> in
    let constraint2 := <{Xs#5 = Xn#5 & Xn#5 <> 31#5}> in <{
      if ! constraint1 & ! constraint2 then {arm_stxp2il_constr size Xn Xs Xt Xt2 (Word 0 1) (Word 0 1)} else
      if constraint1 then
        if unknown 1 then
          (* Constraint_UNDEFINED *) havoc
        else if unknown 1 then
          (* Constraint_NOP *) nop
        else (* Constraint_UNKNOWN or Constraint_NONE *)
        if constraint2 then
          (* Reached Constraint_UNDEFINED and Constraint_NOP above, so don't need to repeat *)
          {arm_stxp2il_constr size Xn Xs Xt Xt2 (Unknown 1) (Unknown 1)}
        else
          {arm_stxp2il_constr size Xn Xs Xt Xt2 (Unknown 1) (Word 0 1)}
        end (* End of constraint1 + constraint2 *)
      end end else
      (* !constraint1 + constraint2 *)
        if unknown 1 then
          (* Constraint_UNDEFINED *) havoc
        else if unknown 1 then
          (* Constraint_NOP *) nop
        else (* Constraint_UNKNOWN or Constraint_NONE *)
          {arm_stxp2il_constr size Xn Xs Xt Xt2 (Word 0 1) (Unknown 1)}
        end end end end}>.

  Definition arm_stxp2il := arm_stxp2il_size.
  Definition arm_stlxp2il := arm_stxp2il_size.

  Definition arm_ldxr2il_size (size Xn Xt:N) :=
    let bytes := N.shiftr size 3 in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end;
      var[Xt] := ucast 64 load[X[Xn],bytes]
    }>.

  Definition arm_ldxrb2il := arm_ldxr2il_size 8.
  Definition arm_ldxrh2il := arm_ldxr2il_size 16.
  Definition arm_ldxr2il := arm_ldxr2il_size.

  Definition arm_ldaxrb2il := arm_ldxr2il_size 8.
  Definition arm_ldaxrh2il := arm_ldxr2il_size 16.
  Definition arm_ldaxr2il := arm_ldxr2il_size.

  Definition arm_ldarb2il := arm_ldxr2il_size 8.
  Definition arm_ldarh2il := arm_ldxr2il_size 16.
  Definition arm_ldar2il := arm_ldxr2il_size.

  Definition arm_ldlarb2il := arm_ldxr2il_size 8.
  Definition arm_ldlarh2il := arm_ldxr2il_size 16.
  Definition arm_ldlar2il := arm_ldxr2il_size.

  Definition arm_ldxp2il_constr (size Xn Xt Xt2:N) (rtunknown:bool) :=
    let bytes := N.shiftr size 2 in
    let datasize := N.shiftl size 1 in
    <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      if {b2exp rtunknown} then var[Xt] := unknown 64 else
      if size#7 = 32#7 then
      (* data *) temp[2000] := load[Xtemp[1000],bytes];
        if BigEndian then
          var[Xt] := ucast 64 (Xtemp[2000][{N.pred datasize}:size]);
          var[Xt2] := ucast 64 (Xtemp[2000][{N.pred size}:0])
        else
          var[Xt] := ucast 64 (Xtemp[2000][{N.pred size}:0]);
          var[Xt2] := ucast 64 (Xtemp[2000][{N.pred datasize}:size])
        end
      else
        if !Aligned[Xtemp[1000],bytes] then exn 0
        else
          var[Xt] := load[Xtemp[1000],8];
          var[Xt2] := load[Xtemp[1000]+8#64,8]
        end
      end
      end
    }>.

  Definition arm_ldxp2il (size Xn Xt Xt2:N) :=
    let constraint_check := <{ Xt#5 = Xt2#5 }> in <{
      if ! constraint_check then {arm_ldxp2il_constr size Xn Xt Xt2 false} else
      (* Constraint_NOP *)
      if unknown 1 then nop else
      (* Constraint_UNDEF *)
      if unknown 1 then havoc else
      (* Constraint_UNKNOWN *)
      {arm_ldxp2il_constr size Xn Xt Xt2 true}
      end end end
    }>.

  Definition load_store_exclusive :=
    let size := n.[30,32] in
    let o2 := n.[23] in
    let l_ := n.[22] in
    let o1 := n.[21] in
    let o0 := n.[15] in
    let Rt2 := n.[10,15] in
    let Rt := n.[0,5] in
    let Rs := n.[16,21] in
    let Rn := n.[5,10] in
    match[bits] size, o2, l_, o1, o0, Rt2 with
    | "-   1  -  1  -  !=11111" => UDF (* Unallocated. - *)
    | "0x  0  -  1  -  !=11111" => UDF (* Unallocated. - *)
    | "00  0  0  0  0  -      " => ARM_EXCLUSIVE ARM_STXRB size Rn Rs Rt Rt2 (* STXRB - *)
    | "00  0  0  0  1  -      " => ARM_EXCLUSIVE ARM_STLXRB size Rn Rs Rt Rt2 (* STLXRB - *)
    | "00  0  0  1  0  11111  " => ARM_EXCLUSIVE ARM_CASP 32 Rn Rs Rt Rt2 (* CASP, CASPA, CASPAL, CASPL - 32-bit, no memory ordering variant on page C6-568 ARMv8.1 *)
    | "00  0  0  1  1  11111  " => ARM_EXCLUSIVE ARM_CASP 32 Rn Rs Rt Rt2 (* CASP, CASPA, CASPAL, CASPL - 32-bit, release variant on page C6-568 ARMv8.1 *)
    | "00  0  1  0  0  -      " => ARM_EXCLUSIVE ARM_LDXRB size Rn Rs Rt Rt2(* LDXRB - *)
    | "00  0  1  0  1  -      " => ARM_EXCLUSIVE ARM_LDAXRB size Rn Rs Rt Rt2(* LDAXRB - *)
    | "00  0  1  1  0  11111  " => ARM_EXCLUSIVE ARM_CASP 32 Rn Rs Rt Rt2 (* CASP, CASPA, CASPAL, CASPL - 32-bit, acquire variant on page C6-568 ARMv8.1 *)
    | "00  0  1  1  1  11111  " => ARM_EXCLUSIVE ARM_CASP 32 Rn Rs Rt Rt2 (* CASP, CASPA, CASPAL, CASPL - 32-bit, acquire and release variant on page C6-568 ARMv8.1 *)
    | "00  1  0  0  0  -      " => ARM_EXCLUSIVE ARM_STLLRB size Rn Rs Rt Rt2 (* STLLRB ARMv8.1 *)
    | "00  1  0  0  1  -      " => ARM_EXCLUSIVE ARM_STLRB size Rn Rs Rt Rt2 (* STLRB - *)
    | "00  1  0  1  0  11111  " => ARM_EXCLUSIVE ARM_CASB size Rn Rs Rt Rt2 (* CASB, CASAB, CASALB, CASLB - No memory ordering variant on page C6-564 ARMv8.1 *)
    | "00  1  0  1  1  11111  " => ARM_EXCLUSIVE ARM_CASB size Rn Rs Rt Rt2 (* CASB, CASAB, CASALB, CASLB - Release variant on page C6-564 ARMv8.1 *)
    | "00  1  1  0  0  -      " => ARM_EXCLUSIVE ARM_LDLARB size Rn Rs Rt Rt2 (* LDLARB ARMv8.1 *)
    | "00  1  1  0  1  -      " => ARM_EXCLUSIVE ARM_LDARB size Rn Rs Rt Rt2 (* LDARB - *)
    | "00  1  1  1  0  11111  " => ARM_EXCLUSIVE ARM_CASB size Rn Rs Rt Rt2 (* CASB, CASAB, CASALB, CASLB - Acquire variant on page C6-564 ARMv8.1 *)
    | "00  1  1  1  1  11111  " => ARM_EXCLUSIVE ARM_CASB size Rn Rs Rt Rt2 (* CASB, CASAB, CASALB, CASLB - Acquire and release variant on page C6-564 ARMv8.1 *)
    | "01  0  0  0  0  -      " => ARM_EXCLUSIVE ARM_STXRH size Rn Rs Rt Rt2(* STXRH - *)
    | "01  0  0  0  1  -      " => ARM_EXCLUSIVE ARM_STLXRH size Rn Rs Rt Rt2 (* STLXRH - *)
    | "01  0  0  1  0  11111  " => ARM_EXCLUSIVE ARM_CASP 32 Rn Rs Rt Rt2 (* CASP, CASPA, CASPAL, CASPL - 64-bit, no memory ordering variant on page C6-569 ARM *)
    | "01  0  0  1  1  11111  " => ARM_EXCLUSIVE ARM_CASP 32 Rn Rs Rt Rt2 (* CASP, CASPA, CASPAL, CASPL - 64-bit, release variant on page C6-569 ARMv8.1 *)
    | "01  0  1  0  0  -      " => ARM_EXCLUSIVE ARM_LDXRH size Rn Rs Rt Rt2 (* LDXRH - *)
    | "01  0  1  0  1  -      " => ARM_EXCLUSIVE ARM_LDAXRH size Rn Rs Rt Rt2 (* LDAXRH - *)
    | "01  0  1  1  0  11111  " => ARM_EXCLUSIVE ARM_CASP 32 Rn Rs Rt Rt2  (* CASP, CASPA, CASPAL, CASPL - 64-bit, acquire variant on *)
    | "01  0  1  1  1  11111  " => ARM_EXCLUSIVE ARM_CASP 32 Rn Rs Rt Rt2  (* CASP, CASPA, CASPAL, CASPL - 64-bit, acquire and *)
    | "01  1  0  0  0  -      " => ARM_EXCLUSIVE ARM_STLLRH size Rn Rs Rt Rt2 (* STLLRH ARMv8.1 *)
    | "01  1  0  0  1  -      " => ARM_EXCLUSIVE ARM_STLRH size Rn Rs Rt Rt2 (* STLRH - *)
    | "01  1  0  1  0  11111  " => ARM_EXCLUSIVE ARM_CASH size Rn Rs Rt Rt2 (* CASH, CASAH, CASALH, CASLH - No memory ordering *)
    | "01  1  0  1  1  11111  " => ARM_EXCLUSIVE ARM_CASH size Rn Rs Rt Rt2 (* CASH, CASAH, CASALH, CASLH - Release variant on *)
    | "01  1  1  0  0  -      " => ARM_EXCLUSIVE ARM_LDLARH size Rn Rs Rt Rt2 (* LDLARH ARMv8.1 *)
    | "01  1  1  0  1  -      " => ARM_EXCLUSIVE ARM_LDARH size Rn Rs Rt Rt2 (* LDARH - *)
    | "01  1  1  1  0  11111  " => ARM_EXCLUSIVE ARM_CASH size Rn Rs Rt Rt2 (* CASH, CASAH, CASALH, CASLH - Acquire variant on *)
    | "01  1  1  1  1  11111  " => ARM_EXCLUSIVE ARM_CASH size Rn Rs Rt Rt2(* CASH, CASAH, CASALH, CASLH - Acquire and release *)
    | "10  0  0  0  0  -      " => ARM_EXCLUSIVE ARM_STXR 32 Rn Rs Rt Rt2(* STXR - 32-bit variant on page C6-922 - *)
    | "10  0  0  0  1  -      " => ARM_EXCLUSIVE ARM_STLXR 32 Rn Rs Rt Rt2 (* STLXR - 32-bit variant on page C6-859 - *)
    | "10  0  0  1  0  -      " => ARM_EXCLUSIVE ARM_STXP 32 Rn Rs Rt Rt2 (* STXP - 32-bit variant on page C6-920 - *)
    | "10  0  0  1  1  -      " => ARM_EXCLUSIVE ARM_STLXP 64 Rn Rs Rt Rt2 (* STLXP - 32-bit variant on page C6-856 - *)
    | "10  0  1  0  0  -      " => ARM_EXCLUSIVE ARM_LDXR 32 Rn Rs Rt Rt2 (* LDXR - 32-bit variant on page C6-750 - *)
    | "10  0  1  0  1  -      " => ARM_EXCLUSIVE ARM_LDAXR 32 Rn Rs Rt Rt2 (* LDAXR - 32-bit variant on page C6-643 - *)
    | "10  0  1  1  0  -      " => ARM_EXCLUSIVE ARM_LDXP 32 Rn Rs Rt Rt2(* LDXP - 32-bit variant on page C6-748 - *)
    | "10  0  1  1  1  -      " => ARM_EXCLUSIVE ARM_LDAXP 32 Rn Rs Rt Rt2 (* LDAXP - 32-bit variant on page C6-641 - *)
    | "10  1  0  0  0  -      " => ARM_EXCLUSIVE ARM_STLLR 64 Rn Rs Rt Rt2 (* STLLR - 32-bit variant on page C6-852 ARMv8.1 *)
    | "10  1  0  0  1  -      " => ARM_EXCLUSIVE ARM_STLR 64 Rn Rs Rt Rt2  (* STLR - 32-bit variant on page C6-853 - *)
    | "10  1  0  1  0  11111  " => ARM_EXCLUSIVE ARM_CAS 32 Rn Rs Rt Rt2  (* CAS, CASA, CASAL, CASL - 32-bit, no memory ordering *)
    | "10  1  0  1  1  11111  " => ARM_EXCLUSIVE ARM_CAS 32 Rn Rs Rt Rt2  (* CAS, CASA, CASAL, CASL - 32-bit, release variant on *)
    | "10  1  1  0  0  -      " => ARM_EXCLUSIVE ARM_LDLAR 32 Rn Rs Rt Rt2(* LDLAR - 32-bit variant on page C6-661 *)
    | "10  1  1  0  1  -      " => ARM_EXCLUSIVE ARM_LDAR 32 Rn Rs Rt Rt2 (* LDAR - 32-bit variant on page C6-638 - *)
    | "10  1  1  1  0  11111  " => ARM_EXCLUSIVE ARM_CAS 32 Rn Rs Rt Rt2 (* CAS, CASA, CASAL, CASL - 32-bit, acquire variant on *)
    | "10  1  1  1  1  11111  " => ARM_EXCLUSIVE ARM_CAS 32 Rn Rs Rt Rt2 (* CAS, CASA, CASAL, CASL - 32-bit, acquire and release *)
    | "11  0  0  0  0  -      " => ARM_EXCLUSIVE ARM_STXR 64 Rn Rs Rt Rt2 (* STXR - 64-bit variant on page C6-922 - *)
    | "11  0  0  0  1  -      " => ARM_EXCLUSIVE ARM_STLXR 64 Rn Rs Rt Rt2 (* STLXR - 64-bit variant on page C6-859 - *)
    | "11  0  0  1  0  -      " => ARM_EXCLUSIVE ARM_STXP 64 Rn Rs Rt Rt2 (* STXP - 64-bit variant on page C6-920 - *)
    | "11  0  0  1  1  -      " => ARM_EXCLUSIVE ARM_STLXP 64 Rn Rs Rt Rt2 (* STLXP - 64-bit variant on page C6-856 - *)
    | "11  0  1  0  0  -      " => ARM_EXCLUSIVE ARM_LDXR 64 Rn Rs Rt Rt2 (* LDXR - 64-bit variant on page C6-750 - *)
    | "11  0  1  0  1  -      " => ARM_EXCLUSIVE ARM_LDAXR 64 Rn Rs Rt Rt2 (* LDAXR - 64-bit variant on page C6-643 - *)
    | "11  0  1  1  0  -      " => ARM_EXCLUSIVE ARM_LDXP 64 Rn Rs Rt Rt2 (* LDXP - 64-bit variant on page C6-748 - *)
    | "11  0  1  1  1  -      " => ARM_EXCLUSIVE ARM_LDAXP 64 Rn Rs Rt Rt2 (* LDAXP - 64-bit variant on page C6-641 - *)
    | "11  1  0  0  0  -      " => ARM_EXCLUSIVE ARM_STLLR 64 Rn Rs Rt Rt2(* STLLR - 64-bit variant on page C6-852 ARMv8.1 *)
    | "11  1  0  0  1  -      " => ARM_EXCLUSIVE ARM_STLR 64 Rn Rs Rt Rt2 (* STLR - 64-bit variant on page C6-853 - *)
    | "11  1  0  1  0  11111  " => ARM_EXCLUSIVE ARM_CAS 64 Rn Rs Rt Rt2 (* CAS, CASA, CASAL, CASL - 64-bit, no memory ordering *)
    | "11  1  0  1  1  11111  " => ARM_EXCLUSIVE ARM_CAS 64 Rn Rs Rt Rt2 (* CAS, CASA, CASAL, CASL - 64-bit, release variant on *)
    | "11  1  1  0  0  -      " => ARM_EXCLUSIVE ARM_LDLAR 64 Rn Rs Rt Rt2 (* LDLAR - 64-bit variant on page C6-661 ARMv8.1 *)
    | "11  1  1  0  1  -      " => ARM_EXCLUSIVE ARM_LDAR 64 Rn Rs Rt Rt2 (* LDAR - 64-bit variant on page C6-638 - *)
    | "11  1  1  1  0  11111  " => ARM_EXCLUSIVE ARM_CAS 64 Rn Rs Rt Rt2 (* CAS, CASA, CASAL, CASL - 64-bit, acquire variant on *)
    | "11  1  1  1  1  11111  " => ARM_EXCLUSIVE ARM_CAS 64 Rn Rs Rt Rt2(* CAS, CASA, CASAL, CASL - 64-bit, acquire and release *)
    else UDF end.

  Definition arm_stlurb2il (Xn Xt imm9:N) :=
    let imm9 := Word imm9 64 in
    let offset := <{scast 64 imm9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      temp[1000] := Xtemp[1000] + offset;
      temp[2000] := X[Xt];
      store[Xtemp[1000],Xtemp[2000],LittleE,1]
    }>.

  (* C6-928 *)
  Definition arm_ldapurb2il Xn Xt imm9 :=
    let offset := <{scast 64 imm9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      temp[1000] := Xtemp[1000] + offset;
      temp[2000] := load[Xtemp[1000],LittleE,1];
      {arm_varid Xt} := ucast 64 Xtemp[2000]
    }>.

  Definition arm_ldapursb2il Xn Xt imm9 (size:N) :=
    let offset := <{scast 64 imm9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      temp[1000] := Xtemp[1000] + offset;
      temp[2000] := load[Xtemp[1000],LittleE,1];
      (* Question: for the 32-bit variant do we only sign-extend up to 32 bits then 0-extend? *)
      {arm_varid Xt} := scast 64 Xtemp[2000]
    }>.

  Definition arm_stlurh2il Xn Xt imm9 :=
    let offset := <{scast 64 imm9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      temp[1000] := Xtemp[1000] + offset;
      temp[2000] := X[Xt];
      (* Question: for the 32-bit variant do we only sign-extend up to 32 bits then 0-extend? *)
      store[Xtemp[1000],Xtemp[2000],LittleE,2]
    }>.

  Definition arm_ldapurh2il Xn Xt imm9 :=
    let offset := <{scast 64 imm9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      temp[1000] := Xtemp[1000] + offset;
      temp[2000] := load[Xtemp[1000],LittleE,1];
      {arm_varid Xt} := ucast 64 Xtemp[2000]
    }>.

  Definition arm_ldapursh2il Xn Xt imm9 (size:N) :=
    let offset := <{scast 64 imm9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      temp[1000] := Xtemp[1000] + offset;
      temp[2000] := load[Xtemp[1000],LittleE,2];
      (* Question: for the 32-bit variant do we only sign-extend up to 32 bits then 0-extend? *)
      {arm_varid Xt} := ucast 64 Xtemp[2000]
    }>.

  Definition arm_stlur2il Xn Xt imm9 (size:N) :=
    let offset := <{scast 64 imm9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      temp[1000] := Xtemp[1000] + offset;
      temp[2000] := X[Xt];
      (* Question: for the 32-bit variant do we only sign-extend up to 32 bits then 0-extend? *)
      store[Xtemp[1000],Xtemp[2000],LittleE,{N.shiftr size 3}]
    }>.

  Definition arm_ldapur2il Xn Xt imm9 (size:N) :=
    let offset := <{scast 64 imm9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      temp[1000] := Xtemp[1000] + offset;
      temp[2000] := load[Xtemp[1000],LittleE,{N.shiftr size 3}];
      (* Question: for the 32-bit variant do we only sign-extend up to 32 bits then 0-extend? *)
      {arm_varid Xt} := Xtemp[2000]
    }>.

  Definition arm_ldapursw2il Xn Xt imm9 (size:N) :=
    let offset := <{scast 64 imm9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      temp[1000] := Xtemp[1000] + offset;
      temp[2000] := load[Xtemp[1000],LittleE,4];
      (* Question: for the 32-bit variant do we only sign-extend up to 32 bits then 0-extend? *)
      {arm_varid Xt} := scast 64 Xtemp[2000]
    }>.

  (*LDAPR/STLR unscaled immediate C4-279*)
  Definition ldapr_stlr_imm_u :=
    let size := n.[30,32] in
    let opc := n.[22,24] in
    let Rn := n.[5,10] in
    let Rt := n.[0,5] in
    let imm9 := n.[12,21] in
    let size := n.[30,32] in
    match[bits] size, opc with
    | "00  00" => ARM_LOAD_GEN ARM_STLURB Rn Rt imm9 size(* STLURB Armv8.4 *)
    | "00  01" => ARM_LOAD_GEN ARM_LDAPURB Rn Rt imm9 size(* LDAPURB Armv8.4 *)
    | "00  10" => ARM_LOAD_GEN ARM_LDAPURSB Rn Rt imm9 64 (* LDAPURSB - 64-bit variant on page C6-932 Armv8.4 *)
    | "00  11" => ARM_LOAD_GEN ARM_LDAPURSB Rn Rt imm9 32 (* LDAPURSB - 32-bit variant on page C6-932 Armv8.4 *)
    | "01  00" => ARM_LOAD_GEN ARM_STLURH Rn Rt imm9 size (* STLURH Armv8.4 *)
    | "01  01" => ARM_LOAD_GEN ARM_LDAPURH Rn Rt imm9 size(* LDAPURH Armv8.4 *)
    | "01  10" => ARM_LOAD_GEN ARM_LDAPURSH Rn Rt imm9 64 (* LDAPURSH - 64-bit variant on page C6-934 Armv8.4 *)
    | "01  11" => ARM_LOAD_GEN ARM_LDAPURSH Rn Rt imm9 32 (* LDAPURSH - 32-bit variant on page C6-934 Armv8.4 *)
    | "10  00" => ARM_LOAD_GEN ARM_STLUR Rn Rt imm9 32 (* STLUR - 32-bit variant on page C6-1219 Armv8.4 *)
    | "10  01" => ARM_LOAD_GEN ARM_LDAPUR Rn Rt imm9 32(* LDAPUR - 32-bit variant on page C6-926 Armv8.4 *)
    | "10  10" => ARM_LOAD_GEN ARM_LDAPURSW Rn Rt imm9 size (* LDAPURSW Armv8.4 *)
    | "10  11" => UDF (* Unallocated. - *)
    | "11  00" => ARM_LOAD_GEN ARM_STLUR Rn Rt imm9 64 (* STLUR - 64-bit variant on page C6-1219 Armv8.4 *)
    | "11  01" => ARM_LOAD_GEN ARM_LDAPUR Rn Rt imm9 64(* LDAPUR - 64-bit variant on page C6-926 Armv8.4 *)
    | "11  10" => UDF (* Unallocated. - *)
    | "11  11" => UDF (* Unallocated. - *)
    else UDF end.

  Definition arm_ldrsw_lit2il Xt imm19 :=
    let offset := <{scast 64 ((imm19 # 21) << (2#21))}> in
    <{temp[1000]:= PC + offset;
    {arm_varid Xt} := scast 64 {MemRead (Xtemp[1000]) 4}}>.

  (* C6-979 *)
  Definition arm_ldr_lit2il Xt imm19 size :=
    let offset := <{scast 64 ((imm19 # 21) << (2#21))}> in
    <{temp[1000]:= PC + offset;
    {arm_varid Xt} := ucast 64 {MemRead (Xtemp[1000]) size}}>.

  (* C6-1138; The effects of PRFM is implementation defined. *)
  Definition arm_prfm_lit2il (Xt imm19:N) := <{havoc}>.
  Definition N_na : N:=0. (* not applicable to this instruction *)
  (* C4-280 *)
  Definition load_reg_literal :=
    let opc := n.[30,32] in
    let Rt := n.[0,5] in
    let imm19 := n.[5,24] in
    let v_ := n.[26] in
    match[bits] opc, v_ with
    | "00  0" => ARM_LD_REG_LIT ARM_LDR_LIT Rt imm19 4 (* LDR (literal) - 32-bit variant on page C6-673 *)
    | "00  1" => UDF (* LDR (literal, SIMD&FP) - 32-bit variant on page C7-1362 *)
    | "01  0" => ARM_LD_REG_LIT ARM_LDR_LIT Rt imm19 8 (* LDR (literal) - 64-bit variant on page C6-673 *)
    | "01  1" => UDF (* LDR (literal, SIMD&FP) - 64-bit variant on page C7-1362 *)
    | "10  0" => ARM_LD_REG_LIT ARM_LDRSW_LIT Rt imm19 N_na (* LDRSW (literal) doesn't actually need size*)
    | "10  1" => UDF (* LDR (literal, SIMD&FP) - 128-bit variant on page C7-1362 *)
    | "11  0" => ARM_LD_REG_LIT ARM_PRFM_LIT Rt imm19 N_na (* PRFM (literal) doesn't actually need size*)
    | "11  1" => UDF (* Unallocated. *)
    else UDF end.

  Definition arm_stnp2il Xn Xt Xt2 imm7 scale :=
    let size := N.shiftl 8 scale in
    let dbytes := N.shiftl 1 scale in
    let offset := <{scast 64 (imm7#7) << (scale # 64)}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      temp[1000] := Xtemp[1000] + offset;
      temp[2000] := X[Xt];
      temp[3000] := X[Xt2];
      {MemWrite (Var (V_TEMP 2000)) dbytes (Var (V_TEMP 2000))};
      temp[1000] := Xtemp[1000] + (dbytes # 64);
      {MemWrite (Var (V_TEMP 2000)) dbytes (Var (V_TEMP 2000))}
    }>.

  Definition arm_ldnp2il_happy Xn Xt Xt2 imm7 scale :=
    let size := N.shiftl 8 scale in
    let dbytes := N.shiftl 1 scale in
    let offset := <{scast 64 (imm7#7) << (scale # 64)}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      temp[1000] := Xtemp[1000] + offset;
      temp[2000] := load[Xtemp[1000], LittleE, dbytes];
      temp[3000] := load[Xtemp[1000]+(dbytes#64), LittleE, dbytes];
      {arm_varid Xt} := Xtemp[2000];
      {arm_varid Xt2} := Xtemp[3000]
    }>.

  Definition arm_ldnp2il Xn Xt Xt2 imm7 scale :=
    <{
      if (Xt # 5) <> (Xt2 # 5) then {arm_ldnp2il_happy Xn Xt Xt2 imm7 scale} else
      (* Constraint_NOP *)
      if unknown 1 then nop else
      (* Constraint_UNDEF *)
      if unknown 1 then havoc else
      (* Constraint_UNKNOWN *)
      {arm_ldnp2il_happy Xn Xt Xt2 imm7 scale};
      {arm_varid Xt} := unknown 64;
      {arm_varid Xt2} := unknown 64
      end end end
    }>.

  Definition arm_stp2il_happy Xn Xt Xt2 imm7 scale wback postindex :=
    let size := N.shiftl 8 scale in
    let dbytes := N.shiftl 1 scale in
    let offset := <{scast 64 (imm7#7) << (scale # 64)}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      if !{b2exp postindex} then temp[1000] := Xtemp[1000] + offset else nop end;
      temp[2000] := X[Xt];
      temp[3000] := X[Xt2];
      store[Xtemp[1000], Xtemp[2000], LittleE, dbytes];
      store[Xtemp[1000]+dbytes#64, Xtemp[2000], LittleE, dbytes];
      if {b2exp wback} then
        temp[1001] := Xtemp[1000];
        if {b2exp postindex} then temp[1001] := Xtemp[1001] + offset else nop end;
        {arm_varid Xn} := Xtemp[1001]
      else
        nop
      end
    }>.

  Definition arm_stp2il Xn Xt Xt2 imm7 scale wback postindex :=
    let size := N.shiftl 8 scale in
    let dbytes := N.shiftl 1 scale in
    let constraint_check := <{ {b2exp wback} & ((Xt#5 = Xn#5) | (Xt#5 = Xn#5)) & (Xn#5 <> 31#5) }> in <{
      if ! constraint_check then {arm_stp2il_happy Xn Xt Xt2 imm7 scale wback postindex} else
      (* Constraint_NOP *)
      if unknown 1 then nop else
      (* Constraint_UNDEF *)
      if unknown 1 then havoc else
      (* Constraint_UNKNOWN *)
      {arm_stp2il_happy Xn Xt Xt2 imm7 scale wback postindex}; (* address in temp[1000] *)
      if Xt#5 = Xn#5 then store[Xtemp[1000],unknown size, LittleE, dbytes] else nop;
      if Xt2#5 = Xn#5 then store[Xtemp[1000]+dbytes#64,unknown size, LittleE, dbytes] else nop
      end end end end end
    }>.

  Definition arm_ldp2il_constr Xn Xt Xt2 imm7 scale wback wb_unknown rt_unknown postindex :=
    let size := N.shiftl 8 scale in
    let dbytes := N.shiftl 1 scale in
    let offset := <{scast 64 (imm7#7) << (scale # 64)}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      if !{b2exp postindex} then temp[1000] := Xtemp[1000] + offset else nop end;
      temp[2000] := load[Xtemp[1000],LittleE,dbytes];
      temp[3000] := load[Xtemp[1000]+dbytes#64,LittleE,dbytes];
      if rt_unknown then temp[2000] := unknown size; temp[3000] := unknown size else nop end;
      {arm_varid Xt} := ucast 64 Xtemp[2000];
      {arm_varid Xt2} := ucast 64 Xtemp[3000];
      if wback then
        if wb_unknown then
          temp[1000] := unknown 64
        else if {b2exp postindex} then temp[1000] := Xtemp[1000] + offset
              else nop
              end
        end;
        {arm_varid Xn} := Xtemp[1000]
      else nop
      end
    }>.

  (* C6-970; semantic deviation for some constraint conditions *)
  Definition arm_ldp2il (Xn Xt Xt2 imm7 scale:N) (wback postindex:bool) :=
    let constraint1 := <{ {b2exp wback} & (Xt#5 = Xn#5 | Xt2#5 = Xn#5) & Xn#5 <> 31#5}> in
    let constraint2 := <{ Xt#5 = Xt2#5 }> in <{
      temp[1] := {b2exp wback}; (* wback *)
      temp[2] := 0#1; (* rt_unknown *)
      temp[3] := 0#1; (* wb_unknown *)
      temp[4] := 0#1; (* NOP *)
      temp[5] := 0#1; (* UNDEF *)
      if constraint1 then
        (* Constraint_WBSUPPRESS *)
        if unknown 1 then temp[1] := 0#1 else
        (* Constraint_UNKNOWN *)
        if unknown 1 then temp[3] := 1#1 else
        (* Constraint_UNDEF *)
        if unknown 1 then temp[5] := 1#1 else
        (* Constraint_NOP *)
        temp[4] := 1#1 end end end
      else nop end;
      if constraint2 then
        (* Constraint_UNKNOWN *)
        if unknown 1 then temp[2] := 1#1 else
        (* Constraint_UNDEF *)
        if unknown 1 then temp[5] := 1#1 else
        (* Constraint_NOP *)
        temp[4] := 1#1 end end
      else nop end;
      if Xtemp[4] then nop else
      if Xtemp[5] then havoc else
        {arm_ldp2il_constr Xn Xt Xt2 imm7 scale <{Xtemp[1]}> <{Xtemp[3]}> <{Xtemp[2]}> postindex}
      end end
    }>.

  Definition arm_stgp2il Xn Xt Xt2 imm7 wback postindex :=
    let offset := <{scast 64 (imm7#7) << LOG2_TAG_GRANULE#64}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      if !{b2exp postindex} then temp[1000] := Xtemp[1000] + offset else nop end;
      temp[2000] := X[Xt];
      temp[3000] := X[Xt2];
      store[Xtemp[1000],Xtemp[2000],LittleE,8];
      store[Xtemp[1000]+8#64,Xtemp[3000],LittleE,8];
      if {b2exp wback} then
        if {b2exp postindex} then temp[1000]:=Xtemp[1000]+offset else nop end;
        {arm_varid Xn} := Xtemp[1000]
      else nop end}>.

  Definition arm_ldpsw2il_constr Xn Xt Xt2 imm7 wback wb_unknown rt_unknown postindex :=
    let offset := <{scast 64 (imm7#7) << (2#64)}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      if !{b2exp postindex} then temp[1000] := Xtemp[1000] + offset else nop end;
      temp[2000] := load[Xtemp[1000],LittleE,4];
      temp[3000] := load[Xtemp[1000]+4#64,LittleE,4];
      if rt_unknown then temp[2000] := unknown 32; temp[3000] := unknown 32 else nop end;
      {arm_varid Xt} := scast 64 Xtemp[2000];
      {arm_varid Xt2} := scast 64 Xtemp[3000];
      if wback then
        if wb_unknown then
          temp[1000] := unknown 64
        else if {b2exp postindex} then temp[1000] := Xtemp[1000] + offset
              else nop
              end
        end;
        {arm_varid Xn} := Xtemp[1000]
      else nop
      end
    }>.

  Definition arm_ldpsw2il (Xn Xt Xt2 imm7:N) (wback postindex:bool) :=
    let constraint1 := <{ {b2exp wback} & (Xt#5 = Xn#5 | Xt2#5 = Xn#5) & Xn#5 <> 31#5}> in
    let constraint2 := <{ Xt#5 = Xt2#5 }> in <{
      temp[1] := {b2exp wback}; (* wback *)
      temp[2] := 0#1; (* rt_unknown *)
      temp[3] := 0#1; (* wb_unknown *)
      temp[4] := 0#1; (* NOP *)
      temp[5] := 0#1; (* UNDEF *)
      if constraint1 then
        (* Constraint_WBSUPPRESS *)
        if unknown 1 then temp[1] := 0#1 else
        (* Constraint_UNKNOWN *)
        if unknown 1 then temp[3] := 1#1 else
        (* Constraint_UNDEF *)
        if unknown 1 then temp[5] := 1#1 else
        (* Constraint_NOP *)
        temp[4] := 1#1 end end end
      else nop end;
      if constraint2 then
        (* Constraint_UNKNOWN *)
        if unknown 1 then temp[2] := 1#1 else
        (* Constraint_UNDEF *)
        if unknown 1 then temp[5] := 1#1 else
        (* Constraint_NOP *)
        temp[4] := 1#1 end end
      else nop end;
      if Xtemp[4] then nop else
      if Xtemp[5] then havoc else
        {arm_ldpsw2il_constr Xn Xt Xt2 imm7 <{Xtemp[1]}> <{Xtemp[3]}> <{Xtemp[2]}> postindex}
      end end
    }>.

  Definition load_store_no_alloc_pair :=
    let opc := n.[30,32] in
    let v_ := n.[26] in
    let l_ := n.[22] in
    let Rt := n.[0,5] in
    let Rn := n.[5,10] in
    let Rt2 := n.[10,15] in
    let imm7 := n.[15,22] in
    match[bits] opc, v_, l_ with
    | "00  0  0" => ARM_STNP Rn Rt Rt2 imm7 2 (* STNP - 32-bit variant on page C6-865 *)
    | "00  0  1" => ARM_LDNP Rn Rt Rt2 imm7 2 (* LDNP - 32-bit variant on page C6-662 *)
    | "00  1  0" => UDF (* STNP (SIMD&FP) - 32-bit variant on page C7-1626 *)
    | "00  1  1" => UDF (* LDNP (SIMD&FP) - 32-bit variant on page C7-1353 *)
    | "01  0  -" => UDF (* Unallocated. *)
    | "01  1  0" => UDF (* STNP (SIMD&FP) - 64-bit variant on page C7-1626 *)
    | "01  1  1" => UDF (* LDNP (SIMD&FP) - 64-bit variant on page C7-1353 *)
    | "10  0  0" => ARM_STNP Rn Rt Rt2 imm7 3 (* STNP - 64-bit variant on page C6-865 *)
    | "10  0  1" => ARM_LDNP Rn Rt Rt2 imm7 3 (* LDNP - 64-bit variant on page C6-662 *)
    | "10  1  0" => UDF (* STNP (SIMD&FP) - 128-bit variant on page C7-1626 *)
    | "10  1  1" => UDF (* LDNP (SIMD&FP) - 128-bit variant on page C7-1353 *)
    | "11  -  -" => UDF (* Unallocated *)
    else UDF end.


  Definition load_store_post_indx_pair :=
    let opc := n.[30,32] in
    let v_ := n.[26] in
    let l_ := n.[22] in
    let Rt := n.[0,5] in
    let Rn := n.[5,10] in
    let Rt2 := n.[10,15] in
    let imm7 := n.[15,22] in
    match[bits] opc, v_, l_ with
    | "00  0  0" => ARM_LD_STR_REG_PAIR ARM_STP Rn Rt Rt2 imm7 2 true true (* STP - 32-bit variant on page C6-867 *)
    | "00  0  1" => ARM_LD_STR_REG_PAIR ARM_LDP Rn Rt Rt2 imm7 2 true true (* LDP - 32-bit variant on page C6-664 *)
    | "00  1  0" => UDF (* STP (SIMD&FP) - 32-bit variant on page C7-1628 *)
    | "00  1  1" => UDF (* LDP (SIMD&FP) - 32-bit variant on page C7-1355 *)
    | "01  0  0" => ARM_LD_STR_REG_PAIR ARM_STGP Rn Rt Rt2 imm7 N_na true true (* Armv8.5 *)
    | "01  0  1" => ARM_LD_STR_REG_PAIR ARM_LDPSW Rn Rt Rt2 imm7 N_na true true (* LDPSW *)
    | "01  1  0" => UDF (* STP (SIMD&FP) - 64-bit variant on page C7-1628 *)
    | "01  1  1" => UDF (* LDP (SIMD&FP) - 64-bit variant on page C7-1355 *)
    | "10  0  0" => ARM_LD_STR_REG_PAIR ARM_STP Rn Rt Rt2 imm7 3 true true (* STP - 64-bit variant on page C6-867 *)
    | "10  0  1" => ARM_LD_STR_REG_PAIR ARM_LDP Rn Rt Rt2 imm7 3 true true (* LDP - 64-bit variant on page C6-664 *)
    | "10  1  0" => UDF (* STP (SIMD&FP) - 128-bit variant on page C7-1628 *)
    | "10  1  1" => UDF (* LDP (SIMD&FP) - 128-bit variant on page C7-1355 *)
    | "11  -  -" => UDF (* Unallocated *)
    else UDF end.

  Definition load_store_pair_offset :=
    let opc := n.[30,32] in
    let v_ := n.[26] in
    let l_ := n.[22] in
    let Rt := n.[0,5] in
    let Rn := n.[5,10] in
    let Rt2 := n.[10,15] in
    let imm7 := n.[15,22] in
    match[bits] opc, v_, l_ with
    | "00  0  0" => ARM_LD_STR_REG_PAIR ARM_STP Rn Rt Rt2 imm7 2 false false (* STP - 32-bit variant on page C6-868 *)
    | "00  0  1" => ARM_LD_STR_REG_PAIR ARM_LDP Rn Rt Rt2 imm7 2 false false (* LDP - 32-bit variant on page C6-665 *)
    | "00  1  0" => UDF (* STP (SIMD&FP) - 32-bit variant on page C7-1629 *)
    | "00  1  1" => UDF (* LDP (SIMD&FP) - 32-bit variant on page C7-1356 *)
    | "01  0  0" => ARM_LD_STR_REG_PAIR ARM_STGP Rn Rt Rt2 imm7 N_na false false (* Unallocated. *)
    | "01  0  1" => ARM_LD_STR_REG_PAIR ARM_LDPSW Rn Rt Rt2 imm7 N_na false false (* LDPSW *)
    | "01  1  0" => UDF (* STP (SIMD&FP) - 64-bit variant on page C7-1629 *)
    | "01  1  1" => UDF (* LDP (SIMD&FP) - 64-bit variant on page C7-1356 *)
    | "10  0  0" => ARM_LD_STR_REG_PAIR ARM_STP Rn Rt Rt2 imm7 3 false false (* STP - 64-bit variant on page C6-868 *)
    | "10  0  1" => ARM_LD_STR_REG_PAIR ARM_LDP Rn Rt Rt2 imm7 3 false false (* LDP - 64-bit variant on page C6-665 *)
    | "10  1  0" => UDF (* STP (SIMD&FP) - 128-bit variant on page C7-1629 *)
    | "10  1  1" => UDF (* LDP (SIMD&FP) - 128-bit variant on page C7-1356 *)
    | "11  -  -" => UDF (* Unallocated. *)
    else UDF end.

  Definition load_store_pre_indx_pair :=
    let opc := n.[30,32] in
    let v_ := n.[26] in
    let l_ := n.[22] in
    let Rt := n.[0,5] in
    let Rn := n.[5,10] in
    let Rt2 := n.[10,15] in
    let imm7 := n.[15,22] in
    match[bits] opc, v_, l_ with
    | "00  0  0" => ARM_LD_STR_REG_PAIR ARM_STP Rn Rt Rt2 imm7 2 true false (* STP - 32-bit variant on page C6-867 *)
    | "00  0  1" => ARM_LD_STR_REG_PAIR ARM_LDP Rn Rt Rt2 imm7 2 true false (* LDP - 32-bit variant on page C6-664 *)
    | "00  1  0" => UDF (* STP (SIMD&FP) - 32-bit variant on page C7-1628 *)
    | "00  1  1" => UDF (* LDP (SIMD&FP) - 32-bit variant on page C7-1355 *)
    | "01  0  0" => ARM_LD_STR_REG_PAIR ARM_STGP Rn Rt Rt2 imm7 N_na true false (* Unallocated. *)
    | "01  0  1" => ARM_LD_STR_REG_PAIR ARM_LDPSW Rn Rt Rt2 imm7 N_na true false (* LDPSW *)
    | "01  1  0" => UDF (* STP (SIMD&FP) - 64-bit variant on page C7-1628 *)
    | "01  1  1" => UDF (* LDP (SIMD&FP) - 64-bit variant on page C7-1355 *)
    | "10  0  0" => ARM_LD_STR_REG_PAIR ARM_STP Rn Rt Rt2 imm7 3 true false (* STP - 64-bit variant on page C6-867 *)
    | "10  0  1" => ARM_LD_STR_REG_PAIR ARM_LDP Rn Rt Rt2 imm7 3 true false (* LDP - 64-bit variant on page C6-664 *)
    | "10  1  0" => UDF (* STP (SIMD&FP) - 128-bit variant on page C7-1628 *)
    | "10  1  1" => UDF (* LDP (SIMD&FP) - 128-bit variant on page C7-1355 *)
    | "11  -  -" => UDF (* Unallocated *)
    else UDF end.

  Definition arm_sturb2il (Xn Xt imm9:N) :=
    let offset := <{scast 64 imm9#9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + offset);
      store[Xtemp[1000],X[Xt],1]
    }>.

  Definition arm_sturh2il (Xn Xt imm9:N) :=
    let offset := <{scast 64 imm9#9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + offset);
      store[Xtemp[1000],X[Xt],2]
    }>.

  Definition arm_stur2il (Xn Xt imm9 size:N) :=
    let offset := <{scast 64 imm9#9}> in
    let bytes := N.shiftr size 3 in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + offset);
      store[Xtemp[1000],X[Xt],bytes]
    }>.

  Definition arm_ldurb2il (Xn Xt imm9:N) :=
    let offset := <{scast 64 imm9#9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + offset);
      var[Xt] := ucast 64 load[Xtemp[1000],1]
    }>.

  Definition arm_ldursb2il (Xn Xt imm9 size:N) :=
    let offset := <{scast 64 imm9#9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + offset);
      var[Xt] := ucast 64 (scast size load[Xtemp[1000],1])
    }>.

  Definition arm_ldurh2il (Xn Xt imm9:N) :=
    let offset := <{scast 64 imm9#9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + offset);
      var[Xt] := ucast 64 load[Xtemp[1000],2]
    }>.

  Definition arm_ldursh2il (Xn Xt imm9 size:N) :=
    let offset := <{scast 64 imm9#9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + offset);
      var[Xt] := ucast 64 (scast size load[Xtemp[1000],2])
    }>.

  Definition arm_ldur2il (Xn Xt imm9 size:N) :=
    let offset := <{scast 64 imm9#9}> in
    let bytes := N.shiftr size 3 in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + offset);
      var[Xt] := ucast 64 load[Xtemp[1000],bytes]
    }>.

  Definition arm_ldursw2il (Xn Xt imm9:N) :=
    let offset := <{scast 64 imm9#9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + offset);
      var[Xt] := scast 64 load[Xtemp[1000],4]
    }>.

  Definition arm_prfum2il (Rn Rt imm9:N) := havoc.

  (*unscaled immediate*)
  Definition load_store_reg_imm_u :=
    let size := n.[30,32] in
    let v_ := n.[26] in
    let opc := n.[22,24] in
    let Rt := n.[0,5] in
    let Rn := n.[5,10] in
    let imm9 := n.[12,21] in
    match[bits] size, v_, opc with
    | "x1  1  1x" => UDF (* Unallocated. *)
    | "00  0  00" => ARM_LOAD_GEN ARM_STURB Rn Rt imm9 size(* STURB *)
    | "00  0  01" => ARM_LOAD_GEN ARM_LDURB Rn Rt imm9 size(* LDURB *)
    | "00  0  10" => ARM_LOAD_GEN ARM_LDURSB Rn Rt imm9 32 (* LDURSB - 64-bit variant on page C6-743 *)
    | "00  0  11" => ARM_LOAD_GEN ARM_LDURSB Rn Rt imm9 64 (* LDURSB - 32-bit variant on page C6-743 *)
    | "00  1  00" => UDF (* STUR (SIMD&FP) - 8-bit variant on page C7-1638 *)
    | "00  1  01" => UDF (* LDUR (SIMD&FP) - 8-bit variant on page C7-1367 *)
    | "00  1  10" => UDF (* STUR (SIMD&FP) - 128-bit variant on page C7-1638 *)
    | "00  1  11" => UDF (* LDUR (SIMD&FP) - 128-bit variant on page C7-1367 *)
    | "01  0  00" => ARM_LOAD_GEN ARM_STURH Rn Rt imm9 size(* STURH *)
    | "01  0  01" => ARM_LOAD_GEN ARM_LDURH Rn Rt imm9 size(* LDURH *)
    | "01  0  10" => ARM_LOAD_GEN ARM_LDURSH Rn Rt imm9 64 (* LDURSH - 64-bit variant on page C6-745 *)
    | "01  0  11" => ARM_LOAD_GEN ARM_LDURSH Rn Rt imm9 32 (* LDURSH - 32-bit variant on page C6-745 *)
    | "01  1  00" => UDF (* STUR (SIMD&FP) - 16-bit variant on page C7-1638 *)
    | "01  1  01" => UDF (* LDUR (SIMD&FP) - 16-bit variant on page C7-1367 *)
    | "1x  0  11" => UDF (* Unallocated. *)
    | "1x  1  1x" => UDF (* Unallocated. *)
    | "10  0  00" => ARM_LOAD_GEN ARM_STUR Rn Rt imm9 32 (* STUR - 32-bit variant on page C6-917 *)
    | "10  0  01" => ARM_LOAD_GEN ARM_LDUR Rn Rt imm9 32 (* LDUR - 32-bit variant on page C6-739 *)
    | "10  0  10" => ARM_LOAD_GEN ARM_LDURSW Rn Rt imm9 size(* LDURSW *)
    | "10  1  00" => UDF (* STUR (SIMD&FP) - 32-bit variant on page C7-1638 *)
    | "10  1  01" => UDF (* LDUR (SIMD&FP) - 32-bit variant on page C7-1367 *)
    | "11  0  00" => ARM_LOAD_GEN ARM_STUR Rn Rt imm9 64 (* STUR - 64-bit variant on page C6-917 *)
    | "11  0  01" => ARM_LOAD_GEN ARM_LDUR Rn Rt imm9 64 (* LDUR - 64-bit variant on page C6-739 *)
    | "11  0  10" => ARM_LOAD_GEN ARM_PRFM Rn Rt imm9 size (* PRFM (unscaled offset) TODO: 0s are a temp placeholder. *)
    | "11  1  00" => UDF (* STUR (SIMD&FP) - 64-bit variant on page C7-1638 *)
    | "11  1  01" => UDF (* LDUR (SIMD&FP) - 64-bit variant on page C7-1367 *)
    else UDF end.

  Definition arm_strb_imm2il_constr (Xn Xt imm912:N) (signed wback postindex rtunknown:bool) :=
    let offset := if signed then <{scast 64 imm912#9}> else <{ucast 64 imm912#12}> in
    let rtunknown := b2exp rtunknown in
    let wback := b2exp wback in
    let postindex := b2exp postindex in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      if !postindex then temp[1000] := Xtemp[1000] + offset else nop end;
      temp[2000] := X[Xt];
      if rtunknown then temp[2000] := ucast 64 unknown 8 else nop end;
      store[Xtemp[1000],Xtemp[2000],1];
      if wback then
        temp[1001] := Xtemp[1000];
        if postindex then temp[1001] := Xtemp[1001] + offset else nop end;
        var[Xn] := Xtemp[1001]
      else
        nop
      end
    }>.

  Definition arm_strb_imm2il (Xn Xt imm912:N) (signed wback postindex:bool) :=
    let wback' := wback in
    let wback := b2exp wback in
    let constraint_check := <{  wback & (Xt#5 = Xn#5) & (Xn#5 <> 31#5) }> in <{
      if ! constraint_check then {arm_strb_imm2il_constr Xn Xt imm912 signed wback' postindex false} else
      (* Constraint_NOP *)
      if unknown 1 then nop else
      (* Constraint_UNDEF *)
      if unknown 1 then havoc else
      (* Constraint_UNKNOWN *)
      {arm_strb_imm2il_constr Xn Xt imm912 signed wback' postindex true}
      end end end
    }>.

  Definition arm_strh_imm2il_constr (Xn Xt imm912:N) (signed wback postindex rtunknown:bool) :=
    let offset := if signed then <{scast 64 imm912#9}> else <{ucast 64 imm912#12}> in
    let rtunknown := b2exp rtunknown in
    let wback := b2exp wback in
    let postindex := b2exp postindex in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      if !postindex then temp[1000] := Xtemp[1000] + offset else nop end;
      temp[2000] := X[Xt];
      if rtunknown then temp[2000] := ucast 64 unknown 16 else nop end;
      store[Xtemp[1000],Xtemp[2000],2];
      if wback then
        temp[1001] := Xtemp[1000];
        if postindex then temp[1001] := Xtemp[1001] + offset else nop end;
        var[Xn] := Xtemp[1001]
      else
        nop
      end
    }>.

  Definition arm_strh_imm2il (Xn Xt imm912 size:N) (signed wback postindex:bool) :=
    let wback' := wback in
    let wback := b2exp wback in
    let constraint_check := <{  wback & (Xt#5 = Xn#5) & (Xn#5 <> 31#5) }> in <{
      if ! constraint_check then {arm_strh_imm2il_constr Xn Xt imm912 signed wback' postindex false} else
      (* Constraint_NOP *)
      if unknown 1 then nop else
      (* Constraint_UNDEF *)
      if unknown 1 then havoc else
      (* Constraint_UNKNOWN *)
      {arm_strh_imm2il_constr Xn Xt imm912 signed wback' postindex true}
      end end end
    }>.


  Definition arm_str_imm2il_constr (Xn Xt imm912 size:N) (signed wback postindex rtunknown:bool) :=
    let offset := if signed then <{scast 64 imm912#9}> else <{ucast 64 imm912#12}> in
    let rtunknown := b2exp rtunknown in
    let wback := b2exp wback in
    let bytes := N.shiftr size 3 in
    let postindex := b2exp postindex in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      if !postindex then temp[1000] := Xtemp[1000] + offset else nop end;
      temp[2000] := X[Xt];
      if rtunknown then temp[2000] := ucast 64 unknown size else nop end;
      store[Xtemp[1000],Xtemp[2000],bytes];
      if wback then
        temp[1001] := Xtemp[1000];
        if postindex then temp[1001] := Xtemp[1001] + offset else nop end;
        var[Xn] := Xtemp[1001]
      else
        nop
      end
    }>.

  Definition arm_str_imm2il (Xn Xt imm912 size:N) (signed wback postindex:bool) :=
    let wback' := wback in
    let wback := b2exp wback in
    let constraint_check := <{  wback & (Xt#5 = Xn#5) & (Xn#5 <> 31#5) }> in <{
      if ! constraint_check then {arm_str_imm2il_constr Xn Xt imm912 size signed wback' postindex false} else
      (* Constraint_NOP *)
      if unknown 1 then nop else
      (* Constraint_UNDEF *)
      if unknown 1 then havoc else
      (* Constraint_UNKNOWN *)
      {arm_str_imm2il_constr Xn Xt imm912 size signed wback' postindex true}
      end end end
    }>.

  Definition arm_ldrb_imm2il_constr (Xn Xt imm912:N) (signed wback postindex wbunknown wbsuppress:bool) :=
    let offset := if signed then <{scast 64 imm912#9}> else <{ucast 64 imm912#12}> in
    let wbunknown := b2exp wbunknown in
    let wbsuppress := b2exp wbsuppress in
    let wback := b2exp wback in
    let postindex := b2exp postindex in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      if !postindex then temp[1000] := Xtemp[1000] + offset else nop end;
      var[Xt] := ucast 64 load[Xtemp[1000],1];
      if wback & !wbsuppress then
        temp[1001] := Xtemp[1000];
        if wbunknown then temp[1001] := unknown 64 else
        if postindex then temp[1001] := Xtemp[1001] + offset
        else nop end end;
        var[Xn] := Xtemp[1001]
      else
        nop
      end
    }>.

  Definition arm_ldrb_imm2il (Xn Xt imm912:N) (signed wback postindex:bool) :=
    let wback' := wback in
    let wback := b2exp wback in
    let constraint_check := <{  wback & (Xt#5 = Xn#5) & (Xn#5 <> 31#5) }> in <{
      if ! constraint_check then {arm_ldrb_imm2il_constr Xn Xt imm912 signed wback' postindex false false} else
      (* Constraint_NOP *)
      if unknown 1 then nop else
      (* Constraint_UNDEF *)
      if unknown 1 then havoc else
      (* Constraint_UNKNOWN *)
      if unknown 1 then {arm_ldrb_imm2il_constr Xn Xt imm912 signed wback' postindex true false} else
      (* Constraint_WBSUPPRESS *)
      {arm_ldrb_imm2il_constr Xn Xt imm912 signed wback' postindex false true}
      end end end end
    }>.

  Definition arm_ldrh_imm2il_constr (Xn Xt imm912:N) (signed wback postindex wbunknown wbsuppress:bool) :=
    let offset := if signed then <{scast 64 imm912#9}> else <{ucast 64 imm912#12}> in
    let wbunknown := b2exp wbunknown in
    let wbsuppress := b2exp wbsuppress in
    let wback := b2exp wback in
    let postindex := b2exp postindex in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      if !postindex then temp[1000] := Xtemp[1000] + offset else nop end;
      var[Xt] := ucast 64 load[Xtemp[1000],2];
      if wback & !wbsuppress then
        temp[1001] := Xtemp[1000];
        if wbunknown then temp[1001] := unknown 64 else
        if postindex then temp[1001] := Xtemp[1001] + offset
        else nop end end;
        var[Xn] := Xtemp[1001]
      else
        nop
      end
    }>.

  Definition arm_ldrh_imm2il (Xn Xt imm912:N) (signed wback postindex:bool) :=
    let wback' := wback in
    let wback := b2exp wback in
    let constraint_check := <{  wback & (Xt#5 = Xn#5) & (Xn#5 <> 31#5) }> in <{
      if ! constraint_check then {arm_ldrh_imm2il_constr Xn Xt imm912 signed wback' postindex false false} else
      (* Constraint_NOP *)
      if unknown 1 then nop else
      (* Constraint_UNDEF *)
      if unknown 1 then havoc else
      (* Constraint_UNKNOWN *)
      if unknown 1 then {arm_ldrh_imm2il_constr Xn Xt imm912 signed wback' postindex true false} else
      (* Constraint_WBSUPPRESS *)
      {arm_ldrh_imm2il_constr Xn Xt imm912 signed wback' postindex false true}
      end end end end
    }>.

  Definition arm_ldr_imm2il_constr (Xn Xt imm912 size:N) (signed wback postindex wbunknown wbsuppress:bool) :=
    let offset := if signed then <{scast 64 imm912#9}> else <{ucast 64 imm912#12}> in
    let bytes := N.shiftr size 3 in
    let wbunknown := b2exp wbunknown in
    let wbsuppress := b2exp wbsuppress in
    let wback := b2exp wback in
    let postindex := b2exp postindex in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      if !postindex then temp[1000] := Xtemp[1000] + offset else nop end;
      var[Xt] := ucast 64 load[Xtemp[1000],bytes];
      if wback & !wbsuppress then
        temp[1001] := Xtemp[1000];
        if wbunknown then temp[1001] := unknown 64 else
        if postindex then temp[1001] := Xtemp[1001] + offset
        else nop end end;
        var[Xn] := Xtemp[1001]
      else
        nop
      end
    }>.

  Definition arm_ldr_imm2il (Xn Xt imm912 size:N) (signed wback postindex:bool) :=
    let wback' := wback in
    let wback := b2exp wback in
    let constraint_check := <{  wback & (Xt#5 = Xn#5) & (Xn#5 <> 31#5) }> in <{
      if ! constraint_check then {arm_ldr_imm2il_constr Xn Xt imm912 size signed wback' postindex false false} else
      (* Constraint_NOP *)
      if unknown 1 then nop else
      (* Constraint_UNDEF *)
      if unknown 1 then havoc else
      (* Constraint_UNKNOWN *)
      if unknown 1 then {arm_ldr_imm2il_constr Xn Xt imm912 size signed wback' postindex true false} else
      (* Constraint_WBSUPPRESS *)
      {arm_ldr_imm2il_constr Xn Xt imm912 size signed wback' postindex false true}
      end end end end
    }>.

  Definition arm_ldrsb_imm2il_constr (Xn Xt imm912 size:N) (signed wback postindex wbunknown wbsuppress:bool) :=
    let offset := if signed then <{scast 64 imm912#9}> else <{ucast 64 imm912#12}> in
    let wbunknown := b2exp wbunknown in
    let wbsuppress := b2exp wbsuppress in
    let wback := b2exp wback in
    let postindex := b2exp postindex in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      if !postindex then temp[1000] := Xtemp[1000] + offset else nop end;
      var[Xt] := ucast 64 (scast size load[Xtemp[1000],1]);
      if wback & !wbsuppress then
        temp[1001] := Xtemp[1000];
        if wbunknown then temp[1001] := unknown 64 else
        if postindex then temp[1001] := Xtemp[1001] + offset
        else nop end end;
        var[Xn] := Xtemp[1001]
      else
        nop
      end
    }>.

  Definition arm_ldrsb_imm2il (Xn Xt imm912 size:N) (signed wback postindex:bool) :=
    let wback' := wback in
    let wback := b2exp wback in
    let constraint_check := <{  wback & (Xt#5 = Xn#5) & (Xn#5 <> 31#5) }> in <{
      if ! constraint_check then {arm_ldrsb_imm2il_constr Xn Xt imm912 size signed wback' postindex false false} else
      (* Constraint_NOP *)
      if unknown 1 then nop else
      (* Constraint_UNDEF *)
      if unknown 1 then havoc else
      (* Constraint_UNKNOWN *)
      if unknown 1 then {arm_ldrsb_imm2il_constr Xn Xt imm912 size signed wback' postindex true false} else
      (* Constraint_WBSUPPRESS *)
      {arm_ldrsb_imm2il_constr Xn Xt imm912 size signed wback' postindex false true}
      end end end end
    }>.

  Definition arm_ldrsh_imm2il_constr (Xn Xt imm912 size:N) (signed wback postindex wbunknown wbsuppress:bool) :=
    let offset := if signed then <{scast 64 imm912#9}> else <{ucast 64 imm912#12}> in
    let wbunknown := b2exp wbunknown in
    let wbsuppress := b2exp wbsuppress in
    let wback := b2exp wback in
    let postindex := b2exp postindex in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      if !postindex then temp[1000] := Xtemp[1000] + offset else nop end;
      var[Xt] := ucast 64 (scast size load[Xtemp[1000],2]);
      if wback & !wbsuppress then
        temp[1001] := Xtemp[1000];
        if wbunknown then temp[1001] := unknown 64 else
        if postindex then temp[1001] := Xtemp[1001] + offset
        else nop end end;
        var[Xn] := Xtemp[1001]
      else
        nop
      end
    }>.

  Definition arm_ldrsh_imm2il (Xn Xt imm912 size:N) (signed wback postindex:bool) :=
    let wback' := wback in
    let wback := b2exp wback in
    let constraint_check := <{  wback & (Xt#5 = Xn#5) & (Xn#5 <> 31#5) }> in <{
      if ! constraint_check then {arm_ldrsh_imm2il_constr Xn Xt imm912 size signed wback' postindex false false} else
      (* Constraint_NOP *)
      if unknown 1 then nop else
      (* Constraint_UNDEF *)
      if unknown 1 then havoc else
      (* Constraint_UNKNOWN *)
      if unknown 1 then {arm_ldrsh_imm2il_constr Xn Xt imm912 size signed wback' postindex true false} else
      (* Constraint_WBSUPPRESS *)
      {arm_ldrsh_imm2il_constr Xn Xt imm912 size signed wback' postindex false true}
      end end end end
    }>.

  Definition arm_ldrsw_imm2il_constr (Xn Xt imm912:N) (signed wback postindex wbunknown wbsuppress:bool) :=
    let offset := if signed then <{scast 64 imm912#9}> else <{ucast 64 imm912#12}> in
    let wbunknown := b2exp wbunknown in
    let wbsuppress := b2exp wbsuppress in
    let wback := b2exp wback in
    let postindex := b2exp postindex in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      if !postindex then temp[1000] := Xtemp[1000] + offset else nop end;
      var[Xt] := scast 64 load[Xtemp[1000],4];
      if wback & !wbsuppress then
        temp[1001] := Xtemp[1000];
        if wbunknown then temp[1001] := unknown 64 else
        if postindex then temp[1001] := Xtemp[1001] + offset
        else nop end end;
        var[Xn] := Xtemp[1001]
      else
        nop
      end
    }>.

  Definition arm_ldrsw_imm2il (Xn Xt imm912:N) (signed wback postindex:bool) :=
    let wback' := wback in
    let wback := b2exp wback in
    let constraint_check := <{  wback & (Xt#5 = Xn#5) & (Xn#5 <> 31#5) }> in <{
      if ! constraint_check then {arm_ldrsw_imm2il_constr Xn Xt imm912 signed wback' postindex false false} else
      (* Constraint_NOP *)
      if unknown 1 then nop else
      (* Constraint_UNDEF *)
      if unknown 1 then havoc else
      (* Constraint_UNKNOWN *)
      if unknown 1 then {arm_ldrsw_imm2il_constr Xn Xt imm912 signed wback' postindex true false} else
      (* Constraint_WBSUPPRESS *)
      {arm_ldrsw_imm2il_constr Xn Xt imm912 signed wback' postindex false true}
      end end end end
    }>.

  (*post-indexed imm*)
  Definition load_store_reg_imm_poi :=
    let size := n.[30,32] in
    let v_ := n.[26] in
    let opc := n.[22,24] in
    let Rt := n.[0,5] in
    let Rn := n.[5,10] in
    let imm9 := n.[12,21] in
    match[bits] size, v_, opc with
    | "x1  1  1x" => UDF (* Unallocated. *)
    | "00  0  00" => ARM_INDEXED ARM_STRB_IMM Rn Rt imm9 size true true true (* STRB (immediate) *)
    | "00  0  01" => ARM_INDEXED ARM_LDRB_IMM Rn Rt imm9 size true true true (* LDRB (immediate) *)
    | "00  0  10" => ARM_INDEXED ARM_LDRSB_IMM Rn Rt imm9 64 true true true (* LDRSB (immediate) - 64-bit variant on page C6-685 *)
    | "00  0  11" => ARM_INDEXED ARM_LDRSB_IMM Rn Rt imm9 32 true true true (* LDRSB (immediate) - 32-bit variant on page C6-685 *)
    | "00  1  00" => UDF (* STR (immediate, SIMD&FP) - 8-bit variant on page C7-1631 *)
    | "00  1  01" => UDF (* LDR (immediate, SIMD&FP) - 8-bit variant on page C7-1358 *)
    | "00  1  10" => UDF (* STR (immediate, SIMD&FP) - 128-bit variant on page C7-1631 *)
    | "00  1  11" => UDF (* LDR (immediate, SIMD&FP) - 128-bit variant on page C7-1358 *)
    | "01  0  00" => ARM_INDEXED ARM_STRH_IMM Rn Rt imm9 64 true true true (* STRH (immediate) *)
    | "01  0  01" => ARM_INDEXED ARM_LDRH_IMM Rn Rt imm9 size true true true (* LDRH (immediate) *)
    | "01  0  10" => ARM_INDEXED ARM_LDRSH_IMM Rn Rt imm9 64 true true true (* LDRSH (immediate) - 64-bit variant on page C6-690 *)
    | "01  0  11" => ARM_INDEXED ARM_LDRSH_IMM Rn Rt imm9 32 true true true (* LDRSH (immediate) - 32-bit variant on page C6-690 *)
    | "01  1  00" => UDF (* STR (immediate, SIMD&FP) - 16-bit variant on page C7-1631 *)
    | "01  1  01" => UDF (* LDR (immediate, SIMD&FP) - 16-bit variant on page C7-1358 *)
    | "1x  0  11" => UDF (* Unallocated. *)
    | "1x  1  1x" => UDF (* Unallocated. *)
    | "10  0  00" => ARM_INDEXED ARM_STR_IMM Rn Rt imm9 32 true true true (* STR (immediate) - 32-bit variant on page C6-870 *)
    | "10  0  01" => ARM_INDEXED ARM_LDR_IMM Rn Rt imm9 32 true true true (* LDR (immediate) - 32-bit variant on page C6-670 *)
    | "10  0  10" => ARM_INDEXED ARM_LDRSW_IMM Rn Rt imm9 size true true true (* LDRSW (immediate) *)
    | "10  1  00" => UDF (* STR (immediate, SIMD&FP) - 32-bit variant on page C7-1631 *)
    | "10  1  01" => UDF (* LDR (immediate, SIMD&FP) - 32-bit variant on page C7-1358 *)
    | "11  0  00" => ARM_INDEXED ARM_STR_IMM Rn Rt imm9 64 true true true (* STR (immediate) - 64-bit variant on page C6-870 *)
    | "11  0  01" => ARM_INDEXED ARM_LDR_IMM Rn Rt imm9 64 true true true (* LDR (immediate) - 64-bit variant on page C6-670 *)
    | "11  0  10" => UDF (* Unallocated. *)
    | "11  1  00" => UDF (* STR (immediate, SIMD&FP) - 64-bit variant on page C7-1631 *)
    | "11  1  01" => UDF (* LDR (immediate, SIMD&FP) - 64-bit variant on page C7-135 *)
    else UDF end.

  Definition arm_sttrb2il (Xn Xt imm9:N) :=
    let offset := <{scast 64 imm9#9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + offset);
      store[Xtemp[1000],X[Xt],1]
    }>.

  Definition arm_sttrh2il (Xn Xt imm9:N) :=
    let offset := <{scast 64 imm9#9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + offset);
      store[Xtemp[1000],X[Xt],2]
    }>.

  Definition arm_sttr2il (Xn Xt imm9 size:N) :=
    let offset := <{scast 64 imm9#9}> in
    let bytes := N.shiftr size 3 in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + offset);
      store[Xtemp[1000],X[Xt],bytes]
    }>.

  Definition arm_ldtrb2il (Xn Xt imm9:N) :=
    let offset := <{scast 64 imm9#9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + offset);
      var[Xt] := ucast 64 load[Xtemp[1000],1]
    }>.

  Definition arm_ldtrh2il (Xn Xt imm9:N) :=
    let offset := <{scast 64 imm9#9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + offset);
      var[Xt] := ucast 64 load[Xtemp[1000],2]
    }>.

  Definition arm_ldtrsb2il (Xn Xt imm9 size:N) :=
    let offset := <{scast 64 imm9#9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + offset);
      var[Xt] := ucast 64 (scast size load[Xtemp[1000],1])
    }>.

  Definition arm_ldtrsh2il (Xn Xt imm9 size:N) :=
    let offset := <{scast 64 imm9#9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + offset);
      var[Xt] := ucast 64 (scast size load[Xtemp[1000],2])
    }>.

  Definition arm_ldtrsw2il (Xn Xt imm9:N) :=
    let offset := <{scast 64 imm9#9}> in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + offset);
      var[Xt] := scast 64 load[Xtemp[1000],4]
    }>.

  Definition arm_ldtr2il (Xn Xt imm9 size:N) :=
    let offset := <{scast 64 imm9#9}> in
    let bytes := N.shiftr size 3 in <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + offset);
      var[Xt] := ucast 64 load[Xtemp[1000],bytes]
    }>.


  (*unprivileged; not encoding privilege checks. E.g., for STTRB:

    unpriv_at_el1 = PSTATE.EL == EL1 && !(EL2Enabled() && HaveNVExt() && HCR_EL2.<NV,NV1> == '11');
    unpriv_at_el2 = PSTATE.EL == EL2 && HaveVirtHostExt() && HCR_EL2.<E2H,TGE> == '11';

    user_access_override = HaveUAOExt() && PSTATE.UAO == '1';
    if !user_access_override && (unpriv_at_el1 || unpriv_at_el2) then
    acctype = AccType_UNPRIV;
    else
    acctype = AccType_NORMAL;
  *)
  Definition load_store_reg_unpriv :=
    let size := n.[30,32] in
    let v_ := n.[26] in
    let opc := n.[22,24] in
    let Rt := n.[0,5] in
    let Rn := n.[5,10] in
    let imm9 := n.[12,21] in
    match[bits] size, v_, opc with
    | "-   1  - " => UDF (* Unallocated. *)
    | "00  0  00" => ARM_REG_UNPRIVILEGED ARM_STTRB Rn Rt imm9 size(* STTRB *)
    | "00  0  01" => ARM_REG_UNPRIVILEGED ARM_LDTRB Rn Rt imm9 size(* LDTRB *)
    | "00  0  10" => ARM_REG_UNPRIVILEGED ARM_LDTRSB Rn Rt imm9 64 (* LDTRSB - 64-bit variant on page C6-722 *)
    | "00  0  11" => ARM_REG_UNPRIVILEGED ARM_LDTRSB Rn Rt imm9 32 (* LDTRSB - 32-bit variant on page C6-722 *)
    | "01  0  00" => ARM_REG_UNPRIVILEGED ARM_STTRH Rn Rt imm9 size(* STTRH *)
    | "01  0  01" => ARM_REG_UNPRIVILEGED ARM_LDTRH Rn Rt imm9 size(* LDTRH *)
    | "01  0  10" => ARM_REG_UNPRIVILEGED ARM_LDTRSH Rn Rt imm9 64 (* LDTRSH - 64-bit variant on page C6-724 *)
    | "01  0  11" => ARM_REG_UNPRIVILEGED ARM_LDTRSH Rn Rt imm9 32 (* LDTRSH - 32-bit variant on page C6-724 *)
    | "1x  0  11" => UDF (* Unallocated. *)
    | "10  0  00" => ARM_REG_UNPRIVILEGED ARM_STTR Rn Rt imm9 32 (* STTR - 32-bit variant on page C6-901 *)
    | "10  0  01" => ARM_REG_UNPRIVILEGED ARM_LDTR Rn Rt imm9 32 (* LDTR - 32-bit variant on page C6-718 *)
    | "10  0  10" => ARM_REG_UNPRIVILEGED ARM_LDTRSW Rn Rt imm9 size(* LDTRSW *)
    | "11  0  00" => ARM_REG_UNPRIVILEGED ARM_STTR Rn Rt imm9 64 (* STTR - 64-bit variant on page C6-901 *)
    | "11  0  01" => ARM_REG_UNPRIVILEGED ARM_LDTR Rn Rt imm9 64 (* LDTR - 64-bit variant on page C6-718 *)
    | "11  0  10" => UDF (* Unallocated. *)
    else UDF end.

  (*pre-indexed imm*)
  Definition load_store_reg_imm_pre  :=
    let size := n.[30,32] in
    let v_ := n.[26] in
    let opc := n.[22,24] in
    let Rt := n.[0,5] in
    let Rn := n.[5,10] in
    let imm9 := n.[12,21] in
    match[bits] size, v_, opc with
    | "x1  1  1x" => UDF (* Unallocated. *)
    | "00  0  00" => ARM_INDEXED ARM_STRB_IMM Rn Rt imm9 size true true false (* STRB (immediate) *)
    | "00  0  01" => ARM_INDEXED ARM_LDRB_IMM Rn Rt imm9 size true true false (* LDRB (immediate) *)
    | "00  0  10" => ARM_INDEXED ARM_LDRSB_IMM Rn Rt imm9 64 true true false (* LDRSB (immediate) - 64-bit variant on page C6-685 *)
    | "00  0  11" => ARM_INDEXED ARM_LDRSB_IMM Rn Rt imm9 32 true true false (* LDRSB (immediate) - 32-bit variant on page C6-685 *)
    | "00  1  00" => UDF (* STR (immediate, SIMD&FP) - 8-bit variant on page C7-1631 *)
    | "00  1  01" => UDF (* LDR (immediate, SIMD&FP) - 8-bit variant on page C7-1358 *)
    | "00  1  10" => UDF (* STR (immediate, SIMD&FP) - 128-bit variant on page C7-1632 *)
    | "00  1  11" => UDF (* LDR (immediate, SIMD&FP) - 128-bit variant on page C7-1359 *)
    | "01  0  00" => ARM_INDEXED ARM_STRH_IMM Rn Rt imm9 size true true false (* STRH (immediate) *)
    | "01  0  01" => ARM_INDEXED ARM_LDRH_IMM Rn Rt imm9 size true true false (* LDRH (immediate) *)
    | "01  0  10" => ARM_INDEXED ARM_LDRSH_IMM Rn Rt imm9 64 true true false (* LDRSH (immediate) - 64-bit variant on page C6-690 *)
    | "01  0  11" => ARM_INDEXED ARM_LDRSH_IMM Rn Rt imm9 32 true true false (* LDRSH (immediate) - 32-bit variant on page C6-690 *)
    | "01  1  00" => UDF (* STR (immediate, SIMD&FP) - 16-bit variant on page C7-1632 *)
    | "01  1  01" => UDF (* LDR (immediate, SIMD&FP) - 16-bit variant on page C7-1359 *)
    | "1x  0  11" => UDF (* Unallocated. *)
    | "1x  1  1x" => UDF (* Unallocated. *)
    | "10  0  00" => ARM_INDEXED ARM_STR_IMM Rn Rt imm9 32 true true false (* STR (immediate) - 32-bit variant on page C6-870 *)
    | "10  0  01" => ARM_INDEXED ARM_LDR_IMM Rn Rt imm9 32 true true false (* LDR (immediate) - 32-bit variant on page C6-670 *)
    | "10  0  10" => ARM_INDEXED ARM_LDRSW_IMM Rn Rt imm9 size true true false (* LDRSW (immediate) *)
    | "10  1  00" => UDF (* STR (immediate, SIMD&FP) - 32-bit variant on page C7-1632 *)
    | "10  1  01" => UDF (* LDR (immediate, SIMD&FP) - 32-bit variant on page C7-1359 *)
    | "11  0  00" => ARM_INDEXED ARM_STR_IMM Rn Rt imm9 64 true true false (* STR (immediate) - 64-bit variant on page C6-870 *)
    | "11  0  01" => ARM_INDEXED ARM_LDR_IMM Rn Rt imm9 64 true true false (* LDR (immediate) - 64-bit variant on page C6-670 *)
    | "11  0  10" => UDF (* Unallocated. *)
    | "11  1  00" => UDF (* STR (immediate, SIMD&FP) - 64-bit variant on page C7-1632 *)
    | "11  1  01" => UDF (* LDR (immediate, SIMD&FP) - 64-bit variant on page C7-1359 *)
    else UDF end.

  (* We assume address translation succeed and is apparent. That is, we do not
     model it. *)
  Definition MemAtomic (op:exp) (w:N) (value address:exp) (rettemp:N):=
    let bytes := N.shiftr w 3 in
    let oldvalue := <{Xtemp[rettemp]}> in
    let nvtemp := N.succ rettemp in
    let newvalue := <{Xtemp[nvtemp]}> in
    <{
      temp[rettemp] := ucast 64 {MemRead address bytes};
      if op = MemAtomicOp_ADD  then temp[nvtemp] := oldvalue + value  else
      if op = MemAtomicOp_BIC  then temp[nvtemp] := oldvalue & !value else
      if op = MemAtomicOp_EOR  then temp[nvtemp] := oldvalue ^ value  else
      if op = MemAtomicOp_ORR  then temp[nvtemp] := oldvalue | value  else
      if op = MemAtomicOp_SMAX then temp[nvtemp] := ite (<{oldvalue s> value}>) oldvalue value else
      if op = MemAtomicOp_SMIN then temp[nvtemp] := ite (<{oldvalue s> value}>) value oldvalue else
      if op = MemAtomicOp_UMAX then temp[nvtemp] := ite (oldvalue  > value) oldvalue value else
      if op = MemAtomicOp_UMIN then temp[nvtemp] := ite (oldvalue  > value) value oldvalue else
      (* op = MemAtomicOP_SWP  *)   temp[nvtemp] := value
      end end end end end end end end;
      store[address,newvalue,bytes]
    }>.

  Definition arm_ldatomic2il_size (op:exp) (size Xn Xs Xt:N) :=
    let address := <{Xtemp[1000]}> in
    let value := <{Xtemp[2000]}> in
    <{
      (* value *) temp[2000]:= ucast 64 (lcast size X[Xs]);
      (* address *) if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      {MemAtomic op size address value 4000};
      if Xt#5 <> 31#5 then var[Xt] := Xtemp[4000] else nop end
    }>.

  Definition arm_ldaddb2il := arm_ldatomic2il_size MemAtomicOp_ADD 8.
  Definition arm_ldaddh2il := arm_ldatomic2il_size MemAtomicOp_ADD 16.
  Definition arm_ldadd2il := arm_ldatomic2il_size MemAtomicOp_ADD.

  Definition arm_ldumaxb2il := arm_ldatomic2il_size MemAtomicOp_UMAX 8.
  Definition arm_ldumaxh2il := arm_ldatomic2il_size MemAtomicOp_UMAX 16.
  Definition arm_ldumax2il := arm_ldatomic2il_size MemAtomicOp_UMAX.

  Definition arm_lduminb2il := arm_ldatomic2il_size MemAtomicOp_UMIN 8.
  Definition arm_lduminh2il := arm_ldatomic2il_size MemAtomicOp_UMIN 16.
  Definition arm_ldumin2il := arm_ldatomic2il_size MemAtomicOp_UMIN.

  Definition arm_ldsmaxb2il := arm_ldatomic2il_size MemAtomicOp_SMAX 8.
  Definition arm_ldsmaxh2il := arm_ldatomic2il_size MemAtomicOp_SMAX 16.
  Definition arm_ldsmax2il := arm_ldatomic2il_size MemAtomicOp_SMAX.

  Definition arm_ldsminb2il := arm_ldatomic2il_size MemAtomicOp_SMIN 8.
  Definition arm_ldsminh2il := arm_ldatomic2il_size MemAtomicOp_SMIN 16.
  Definition arm_ldsmin2il := arm_ldatomic2il_size MemAtomicOp_SMIN.

  Definition arm_ldclrb2il := arm_ldatomic2il_size MemAtomicOp_BIC 8.
  Definition arm_ldclrh2il := arm_ldatomic2il_size MemAtomicOp_BIC 16.
  Definition arm_ldclr2il := arm_ldatomic2il_size MemAtomicOp_BIC.

  Definition arm_ldsetb2il := arm_ldatomic2il_size MemAtomicOp_ORR 8.
  Definition arm_ldseth2il := arm_ldatomic2il_size MemAtomicOp_ORR 16.
  Definition arm_ldset2il := arm_ldatomic2il_size MemAtomicOp_ORR.

  Definition arm_ldeorb2il := arm_ldatomic2il_size MemAtomicOp_EOR 8.
  Definition arm_ldeorh2il := arm_ldatomic2il_size MemAtomicOp_EOR 16.
  Definition arm_ldeor2il := arm_ldatomic2il_size MemAtomicOp_EOR.

  (* Unlike the other ld atomic operations, swap can write to SP (C6-1331). *)
  Definition arm_swp2il_size (op:exp) (size Xn Xs Xt:N) :=
    let address := <{Xtemp[1000]}> in
    let value := <{Xtemp[2000]}> in
    <{
      (* value *) temp[2000]:= ucast 64 (lcast size X[Xs]);
      (* address *) if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      {MemAtomic op size address value 4000};
      var[Xt] := Xtemp[4000]
    }>.

  Definition arm_swpb2il := arm_swp2il_size MemAtomicOp_SWP 8.
  Definition arm_swph2il := arm_swp2il_size MemAtomicOp_SWP 16.
  Definition arm_swp2il := arm_swp2il_size MemAtomicOp_SWP.

  Definition arm_ldapr2il_size (size Xn Xt:N) :=
    let bytes := N.shiftr size 3 in  <{
      (* address *) if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      var[Xt] := {MemRead <{Xtemp[1000]}> bytes}
    }>.

  Definition arm_ldaprb2il := arm_ldapr2il_size 8.
  Definition arm_ldaprh2il := arm_ldapr2il_size 16.
  Definition arm_ldapr2il := arm_ldapr2il_size.


  (*atomic memory ops*)
  Definition atomic  :=
    let size := n.[30,32] in
    let v_ := n.[26] in
    let a_ := n.[23] in
    let r_ := n.[22] in
    let o3 := n.[15] in
    let opc := n.[12,15] in
    let Rt := n.[0,5] in
    let Rn := n.[5,10] in
    let Rs := n.[16,21] in
    match[bits] size, v_, a_, r_, o3, opc with
    | "-   0  -  -  1  001" => UDF (* Unallocated. - *)
    | "-   0  -  -  1  01x" => UDF (* Unallocated. - *)
    | "-   0  -  -  1  101" => UDF (* Unallocated. - *)
    | "-   0  -  -  1  11x" => UDF (* Unallocated. - *)
    | "-   0  0  -  1  100" => UDF (* Unallocated. - *)
    | "-   0  1  1  1  100" => UDF (* Unallocated. - *)
    | "-   1  -  -  -  -  " => UDF (* Unallocated. - *)
    | "00  0  0  0  0  000" => ARM_ATOMIC ARM_LDADDB  size Rn Rs Rt (* LDADDB, LDADDAB, LDADDALB, LDADDLB - No memory ordering variant on page C6-632 ARMv8.1 *)
    | "00  0  0  0  0  001" => ARM_ATOMIC ARM_LDCLRB  size Rn Rs Rt (* LDCLRB, LDCLRAB, LDCLRALB, LDCLRLB -  *)
    | "00  0  0  0  0  010" => ARM_ATOMIC ARM_LDEORB  size Rn Rs Rt (* LDEORB, LDEORAB, LDEORALB, LDEORLB - No *)
    | "00  0  0  0  0  011" => ARM_ATOMIC ARM_LDSETB  size Rn Rs Rt (* LDSETB, LDSETAB, LDSETALB, LDSETLB - No *)
    | "00  0  0  0  0  100" => ARM_ATOMIC ARM_LDSMAXB size Rn Rs Rt (* LDSMAXB, LDSMAXAB, LDSMAXALB, LDSMAXLB - ARMv8.1 *)
    | "00  0  0  0  0  101" => ARM_ATOMIC ARM_LDSMINB size Rn Rs Rt (* LDSMINB, LDSMINAB, LDSMINALB, LDSMINLB *)
    | "00  0  0  0  0  110" => ARM_ATOMIC ARM_LDUMAXB size Rn Rs Rt (* LDUMAXB, LDUMAXAB, LDUMAXALB, LDUMAXLB - ARMv8.1 *)
    | "00  0  0  0  0  111" => ARM_ATOMIC ARM_LDUMINB size Rn Rs Rt (* LDUMINB, LDUMINAB, LDUMINALB, LDUMINLB - ARMv8.1 *)
    | "00  0  0  0  1  000" => ARM_ATOMIC ARM_SWPB size Rn Rs Rt (* SWPB, SWPAB, SWPALB, SWPLB - No memory ordering variant on page C6-941 *)
    | "00  0  0  1  0  000" => ARM_ATOMIC ARM_LDADDB size Rn Rs Rt (* LDADDB, LDADDAB, LDADDALB, LDADDLB - Release variant on page C6-632 *)
    | "00  0  0  1  0  001" => ARM_ATOMIC ARM_LDCLRB size Rn Rs Rt (* LDCLRB, LDCLRAB, LDCLRALB, LDCLRLB - Release variant on page C6-647 *)
    | "00  0  0  1  0  010" => ARM_ATOMIC ARM_LDEORB size Rn Rs Rt (* LDEORB, LDEORAB, LDEORALB, LDEORLB - *)
    | "00  0  0  1  0  011" => ARM_ATOMIC ARM_LDSETB size Rn Rs Rt (* LDSETB, LDSETAB, LDSETALB, LDSETLB - *)
    | "00  0  0  1  0  100" => ARM_ATOMIC ARM_LDSMAXB size Rn Rs Rt (* LDSMAXB, LDSMAXAB, LDSMAXALB, *)
    | "00  0  0  1  0  101" => ARM_ATOMIC ARM_LDSMINB size Rn Rs Rt (* LDSMINB, LDSMINAB, LDSMINALB, LDSMINLB *)
    | "00  0  0  1  0  110" => ARM_ATOMIC ARM_LDUMAXB size Rn Rs Rt (* LDUMAXB, LDUMAXAB, LDUMAXALB, LDUMAXLB - Release variant on page C6-727 *)
    | "00  0  0  1  0  111" => ARM_ATOMIC ARM_LDUMINB size Rn Rs Rt (* LDUMINB, LDUMINAB, LDUMINALB, LDUMINLB - Release variant on page C6-733 ARMv8.1 *)
    | "00  0  0  1  1  000" => ARM_ATOMIC ARM_SWPB size Rn Rs Rt (* SWPB, SWPAB, SWPALB, SWPLB - Release variant on page C6-941 ARMv8.1 *)
    | "00  0  1  0  0  000" => ARM_ATOMIC ARM_LDADDB size Rn Rs Rt (* LDADDB, LDADDAB, LDADDALB, LDADDLB - Acquire variant on page C6-632 ARMv8.1 *)
    | "00  0  1  0  0  001" => ARM_ATOMIC ARM_LDCLRB size Rn Rs Rt (* LDCLRB, LDCLRAB, LDCLRALB, LDCLRLB - Acquire variant on page C6-647 ARMv8.1 *)
    | "00  0  1  0  0  010" => ARM_ATOMIC ARM_LDEORB size Rn Rs Rt (* LDEORB, LDEORAB, LDEORALB, LDEORLB - Acquire variant on page C6-653 ARMv8.1 *)
    | "00  0  1  0  0  011" => ARM_ATOMIC ARM_LDSETB size Rn Rs Rt (* LDSETB, LDSETAB, LDSETALB, LDSETLB - Acquire variant on page C6-700 ARMv8.1 *)
    | "00  0  1  0  0  100" => ARM_ATOMIC ARM_LDSMAXB size Rn Rs Rt (* LDSMAXB, LDSMAXAB, LDSMAXALB, LDSMAXLB - Acquire variant on page C6-706 ARMv8.1 *)
    | "00  0  1  0  0  101" => ARM_ATOMIC ARM_LDSMINB size Rn Rs Rt (* LDSMINB, LDSMINAB, LDSMINALB, LDSMINLB - Acquire variant on page C6-712 ARMv8.1 *)
    | "00  0  1  0  0  110" => ARM_ATOMIC ARM_LDUMAXB size Rn Rs Rt (* LDUMAXB, LDUMAXAB, LDUMAXALB, LDUMAXLB - Acquire variant on page C6-727 ARMv8.1 *)
    | "00  0  1  0  0  111" => ARM_ATOMIC ARM_LDUMINB size Rn Rs Rt (* LDUMINB, LDUMINAB, LDUMINALB, LDUMINLB - Acquire variant on page C6-733 *)
    | "00  0  1  0  1  000" => ARM_ATOMIC ARM_SWPB size Rn Rs Rt (* SWPB, SWPAB, SWPALB, SWPLB - Acquire varianton page C6-941 *)
    | "00  0  1  0  1  100" => ARM_ATOMIC ARM_LDAPR size Rn Rs Rt (* Manually added, what is this LDAPRB doing in the atomic table? Its encoding matches. *)
    | "00  0  1  1  0  000" => ARM_ATOMIC ARM_LDADDB size Rn Rs Rt (* LDADDB, LDADDAB, LDADDALB, LDADDLB - and release variant on page C6-632 *)
    | "00  0  1  1  0  001" => ARM_ATOMIC ARM_LDCLRB size Rn Rs Rt (* LDCLRB, LDCLRAB, LDCLRALB, LDCLRLB - and release variant on page C6-647 *)
    | "00  0  1  1  0  010" => ARM_ATOMIC ARM_LDEORB size Rn Rs Rt (* LDEORB, LDEORAB, LDEORALB, LDEORLB - and release variant on page C6-653 *)
    | "00  0  1  1  0  011" => ARM_ATOMIC ARM_LDSETB size Rn Rs Rt (* LDSETB, LDSETAB, LDSETALB, LDSETLB - and release variant on page C6-700 *)
    | "00  0  1  1  0  100" => ARM_ATOMIC ARM_LDSMAXB size Rn Rs Rt (* LDSMAXB, LDSMAXAB, LDSMAXALB,LDSMAXLB - Acquire and release variant on C6-706 *)
    | "00  0  1  1  0  101" => ARM_ATOMIC ARM_LDSMINB size Rn Rs Rt (* LDSMINB, LDSMINAB, LDSMINALB, LDSMINLB- Acquire and release variant on page C6-712 *)
    | "00  0  1  1  0  110" => ARM_ATOMIC ARM_LDUMAXB size Rn Rs Rt (* LDUMAXB, LDUMAXAB, LDUMAXALB,LDUMAXLB - Acquire and release variant on C6-727 *)
    | "00  0  1  1  0  111" => ARM_ATOMIC ARM_LDUMINB size Rn Rs Rt (* LDUMINB, LDUMINAB, LDUMINALB,LDUMINLB - Acquire and release variant on C6-733 *)
    | "00  0  1  1  1  000" => ARM_ATOMIC ARM_SWPB size Rn Rs Rt (* SWPB, SWPAB, SWPALB, SWPLB - Acquire and variant on page C6-941 *)
    | "01  0  0  0  0  000" => ARM_ATOMIC ARM_LDADDH size Rn Rs Rt (* LDADDH, LDADDAH, LDADDALH, LDADDLH - memory ordering variant on page C6-634 *)
    | "01  0  0  0  0  001" => ARM_ATOMIC ARM_LDCLRH size Rn Rs Rt (* LDCLRH, LDCLRAH, LDCLRALH, LDCLRLH - No ordering variant on page C6-649 *)
    | "01  0  0  0  0  010" => ARM_ATOMIC ARM_LDEORH size Rn Rs Rt (* LDEORH, LDEORAH, LDEORALH, LDEORLH - No memory ordering variant on page C6-655 *)
    | "01  0  0  0  0  011" => ARM_ATOMIC ARM_LDSETH size Rn Rs Rt (* LDSETH, LDSETAH, LDSETALH, LDSETLH - No *)
    | "01  0  0  0  0  100" => ARM_ATOMIC ARM_LDSMAXH size Rn Rs Rt (* LDSMAXH, LDSMAXAH, LDSMAXALH, LDSMAXLH - No memory ordering variant on *)
    | "01  0  0  0  0  101" => ARM_ATOMIC ARM_LDSMINH size Rn Rs Rt (* LDSMINH, LDSMINAH, LDSMINALH, LDSMINLH *)
    | "01  0  0  0  0  110" => ARM_ATOMIC ARM_LDUMAXH size Rn Rs Rt (* LDUMAXH, LDUMAXAH, LDUMAXALH, LDUMAXLH - No memory ordering variant on *)
    | "01  0  0  0  0  111" => ARM_ATOMIC ARM_LDUMINH size Rn Rs Rt (* LDUMINH, LDUMINAH, LDUMINALH, LDUMINLH - No memory ordering variant on *)
    | "01  0  0  0  1  000" => ARM_ATOMIC ARM_SWPH size Rn Rs Rt (* SWPH, SWPAH, SWPALH, SWPLH - No memory ordering variant on page C6-943 *)
    | "01  0  0  1  0  000" => ARM_ATOMIC ARM_LDADDH size Rn Rs Rt (* LDADDH, LDADDAH, LDADDALH, LDADDLH - *)
    | "01  0  0  1  0  001" => ARM_ATOMIC ARM_LDCLRH size Rn Rs Rt (* LDCLRH, LDCLRAH, LDCLRALH, LDCLRLH - *)
    | "01  0  0  1  0  010" => ARM_ATOMIC ARM_LDEORH size Rn Rs Rt (* LDEORH, LDEORAH, LDEORALH, LDEORLH - *)
    | "01  0  0  1  0  011" => ARM_ATOMIC ARM_LDSETH size Rn Rs Rt (* LDSETH, LDSETAH, LDSETALH, LDSETLH - *)
    | "01  0  0  1  0  100" => ARM_ATOMIC ARM_LDSMAXH size Rn Rs Rt (* LDSMAXH, LDSMAXAH, LDSMAXALH,LDSMAXLH - Release variant on page C6-708 *)
    | "01  0  0  1  0  101" => ARM_ATOMIC ARM_LDSMINH size Rn Rs Rt (* LDSMINH, LDSMINAH, LDSMINALH, LDSMINLH *)
    | "01  0  0  1  0  110" => ARM_ATOMIC ARM_LDUMAXH size Rn Rs Rt (* LDUMAXH, LDUMAXAH, LDUMAXALH, LDUMAXLH - Release variant on page C6-729 *)
    | "01  0  0  1  0  111" => ARM_ATOMIC ARM_LDUMINH size Rn Rs Rt (* LDUMINH, LDUMINAH, LDUMINALH, LDUMINLH - Release variant on page C6-735 *)
    | "01  0  0  1  1  000" => ARM_ATOMIC ARM_SWPH size Rn Rs Rt (* SWPH, SWPAH, SWPALH, SWPLH - Release variant *)
    | "01  0  1  0  0  000" => ARM_ATOMIC ARM_LDADDH size Rn Rs Rt (* LDADDH, LDADDAH, LDADDALH, LDADDLH - *)
    | "01  0  1  0  0  001" => ARM_ATOMIC ARM_LDCLRH size Rn Rs Rt (* LDCLRH, LDCLRAH, LDCLRALH, LDCLRLH - *)
    | "01  0  1  0  0  010" => ARM_ATOMIC ARM_LDEORH size Rn Rs Rt (* LDEORH, LDEORAH, LDEORALH, LDEORLH - *)
    | "01  0  1  0  0  011" => ARM_ATOMIC ARM_LDSETH size Rn Rs Rt (* LDSETH, LDSETAH, LDSETALH, LDSETLH - *)
    | "01  0  1  0  0  100" => ARM_ATOMIC ARM_LDSMAXH size Rn Rs Rt (* LDSMAXH, LDSMAXAH, LDSMAXALH, LDSMAXLH - Acquire variant on page C6-708 *)
    | "01  0  1  0  0  101" => ARM_ATOMIC ARM_LDSMINH size Rn Rs Rt (* LDSMINH, LDSMINAH, LDSMINALH, LDSMINLH *)
    | "01  0  1  0  0  110" => ARM_ATOMIC ARM_LDUMAXH size Rn Rs Rt (* LDUMAXH, LDUMAXAH, LDUMAXALH, LDUMAXLH - Acquire variant on page C6-729 *)
    | "01  0  1  0  0  111" => ARM_ATOMIC ARM_LDUMINH size Rn Rs Rt (* LDUMINH, LDUMINAH, LDUMINALH, LDUMINLH - Acquire variant on page C6-735 *)
    | "01  0  1  0  1  000" => ARM_ATOMIC ARM_SWPH size Rn Rs Rt (* SWPH, SWPAH, SWPALH, SWPLH - Acquire variant *)
    | "01  0  1  0  1  100" => ARM_ATOMIC ARM_LDAPRH size Rn Rs Rt (* LDAPR... *)
    | "01  0  1  1  0  000" => ARM_ATOMIC ARM_LDADDH size Rn Rs Rt (* LDADDH, LDADDAH, LDADDALH, LDADDLH - *)
    | "01  0  1  1  0  001" => ARM_ATOMIC ARM_LDCLRH size Rn Rs Rt (* LDCLRH, LDCLRAH, LDCLRALH, LDCLRLH - *)
    | "01  0  1  1  0  010" => ARM_ATOMIC ARM_LDEORH size Rn Rs Rt (* LDEORH, LDEORAH, LDEORALH, LDEORLH - *)
    | "01  0  1  1  0  011" => ARM_ATOMIC ARM_LDSETH size Rn Rs Rt (* LDSETH, LDSETAH, LDSETALH, LDSETLH - *)
    | "01  0  1  1  0  100" => ARM_ATOMIC ARM_LDSMAXH size Rn Rs Rt (* LDSMAXH, LDSMAXAH, LDSMAXALH,LDSMAXLH  *)
    | "01  0  1  1  0  101" => ARM_ATOMIC ARM_LDSMINH size Rn Rs Rt (* LDSMINH, LDSMINAH, LDSMINALH, LDSMINLH- Acquire and release variant on page C6-714 *)
    | "01  0  1  1  0  110" => ARM_ATOMIC ARM_LDUMAXH size Rn Rs Rt (* LDUMAXH, LDUMAXAH, LDUMAXALH, LDUMAXLH - Acquire and release variant on *)
    | "01  0  1  1  0  111" => ARM_ATOMIC ARM_LDUMINH size Rn Rs Rt (* LDUMINH, LDUMINAH, LDUMINALH, LDUMINLH - Acquire and release variant on *)
    | "01  0  1  1  1  000" => ARM_ATOMIC ARM_SWPH size Rn Rs Rt (* SWPH, SWPAH, SWPALH, SWPLH - Acquire and *)
    | "10  0  0  0  0  000" => ARM_ATOMIC ARM_LDADD 32 Rn Rs Rt (* LDADD, LDADDA, LDADDAL, LDADDL - 32-bit, *)
    | "10  0  0  0  0  001" => ARM_ATOMIC ARM_LDCLR 32 Rn Rs Rt (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 32-bit, no *)
    | "10  0  0  0  0  010" => ARM_ATOMIC ARM_LDEOR 32 Rn Rs Rt (* LDEOR, LDEORA, LDEORAL, LDEORL - 32-bit, no *)
    | "10  0  0  0  0  011" => ARM_ATOMIC ARM_LDSET 32 Rn Rs Rt (* LDSET, LDSETA, LDSETAL, LDSETL - 32-bit, no *)
    | "10  0  0  0  0  100" => ARM_ATOMIC ARM_LDSMAX 32 Rn Rs Rt (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL - 32-bit, no memory ordering variant on page C6-710 *)
    | "10  0  0  0  0  101" => ARM_ATOMIC ARM_LDSMIN 32 Rn Rs Rt (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL - 32-bit, no memory ordering variant on page C6-716 *)
    | "10  0  0  0  0  110" => ARM_ATOMIC ARM_LDUMAX 32 Rn Rs Rt (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL - 32-bit, no memory ordering variant on page C6-731 *)
    | "10  0  0  0  0  111" => ARM_ATOMIC ARM_LDUMIN 32 Rn Rs Rt (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL  *)
    | "10  0  0  0  1  000" => ARM_ATOMIC ARM_SWP 32 Rn Rs Rt (* SWP, SWPA, SWPAL, SWPL - 32-bit, no memory ordering variant on page C6-945 ARMv8.1 *)
    | "10  0  0  1  0  000" => ARM_ATOMIC ARM_LDADD 32 Rn Rs Rt (* LDADD, LDADDA, LDADDAL, LDADDL - 32-bit, release variant on page C6-636 ARMv8.1 *)
    | "10  0  0  1  0  001" => ARM_ATOMIC ARM_LDCLR 32 Rn Rs Rt (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 32-bit, release variant on page C6-651 ARMv8.1 *)
    | "10  0  0  1  0  010" => ARM_ATOMIC ARM_LDEOR 32 Rn Rs Rt (* LDEOR, LDEORA, LDEORAL, LDEORL - 32-bit, release variant on page C6-657 ARMv8.1 *)
    | "10  0  0  1  0  011" => ARM_ATOMIC ARM_LDSET 32 Rn Rs Rt (* LDSET, LDSETA, LDSETAL, LDSETL - 32-bit, release variant on page C6-704 ARMv8.1 *)
    | "10  0  0  1  0  100" => ARM_ATOMIC ARM_LDSMAX 32 Rn Rs Rt (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL - 32-bit, release variant on page C6-710 ARMv8.1 *)
    | "10  0  0  1  0  101" => ARM_ATOMIC ARM_LDSMIN 32 Rn Rs Rt (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL - 32-bit, release variant on page C6-716 ARMv8.1 *)
    | "10  0  0  1  0  110" => ARM_ATOMIC ARM_LDUMAX 32 Rn Rs Rt (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL - 32-bit, release variant on page C6-731 ARMv8.1 *)
    | "10  0  0  1  0  111" => ARM_ATOMIC ARM_LDUMIN 32 Rn Rs Rt (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL - 32-bit, release variant on page C6-737 ARMv8.1 *)
    | "10  0  0  1  1  000" => ARM_ATOMIC ARM_SWP 32 Rn Rs Rt (* SWP, SWPA, SWPAL, SWPL - 32-bit, release variant on page C6-945 ARMv8.1 *)
    | "10  0  1  0  0  000" => ARM_ATOMIC ARM_LDADD 32 Rn Rs Rt (* LDADD, LDADDA, LDADDAL, LDADDL - 32-bit, *)
    | "0   0  1  0  0  001" => ARM_ATOMIC ARM_LDCLR 32 Rn Rs Rt (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 32-bit, acquire variant on page C6-651 ARMv8.1 *)
    | "10  0  1  0  0  010" => ARM_ATOMIC ARM_LDEOR 32 Rn Rs Rt (* LDEOR, LDEORA, LDEORAL, LDEORL - 32-bit, acquire variant on page C6-657 ARMv8.1 *)
    | "10  0  1  0  0  011" => ARM_ATOMIC ARM_LDSET 32 Rn Rs Rt (* LDSET, LDSETA, LDSETAL, LDSETL - 32-bit, acquire variant on page C6-704 ARMv8.1 *)
    | "10  0  1  0  0  100" => ARM_ATOMIC ARM_LDSMAX 32 Rn Rs Rt (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL - 32-bit, acquire variant on page C6-710 ARMv8.1 *)
    | "10  0  1  0  0  101" => ARM_ATOMIC ARM_LDSMIN 32 Rn Rs Rt (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL - 32-bit, acquire variant on page C6-716 ARMv8.1 *)
    | "10  0  1  0  0  110" => ARM_ATOMIC ARM_LDUMAX 32 Rn Rs Rt (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL - 32-bit, acquire variant on page C6-731 ARMv8.1 *)
    | "10  0  1  0  0  111" => ARM_ATOMIC ARM_LDUMIN 32 Rn Rs Rt (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL - 32-bit, acquire variant on page C6-737 ARMv8.1 *)
    | "10  0  1  0  1  000" => ARM_ATOMIC ARM_SWP 32 Rn Rs Rt (* SWP, SWPA, SWPAL, SWPL - 32-bit, acquire variant on page C6-945 ARMv8.1 *)
    | "10  0  1  0  1  100" => ARM_ATOMIC ARM_LDAPR 32 Rn Rs Rt (* LDAPR... *)
    | "10  0  1  1  0  000" => ARM_ATOMIC ARM_LDADD 32 Rn Rs Rt (* LDADD, LDADDA, LDADDAL, LDADDL - 32-bit, acquire and release variant on page C6-636 ARMv8.1 *)
    | "10  0  1  1  0  001" => ARM_ATOMIC ARM_LDCLR 32 Rn Rs Rt (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 32-bit, acquire and release variant on page C6-651 ARMv8.1 *)
    | "10  0  1  1  0  010" => ARM_ATOMIC ARM_LDEOR 32 Rn Rs Rt (* LDEOR, LDEORA, LDEORAL, LDEORL - 32-bit, acquire and release variant on page C6-657 ARMv8.1 *)
    | "10  0  1  1  0  011" => ARM_ATOMIC ARM_LDSET 32 Rn Rs Rt (* LDSET, LDSETA, LDSETAL, LDSETL - 32-bit, acquire and release variant on page C6-704 ARMv8.1 *)
    | "10  0  1  1  0  100" => ARM_ATOMIC ARM_LDSMAX 32 Rn Rs Rt (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL - 32-bit, acquire and release variant on page C6-710 ARMv8.1 *)
    | "10  0  1  1  0  101" => ARM_ATOMIC ARM_LDSMIN 32 Rn Rs Rt (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL - 32-bit, acquire and release variant on page C6-716 ARMv8.1 *)
    | "10  0  1  1  0  110" => ARM_ATOMIC ARM_LDUMAX 32 Rn Rs Rt (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL - 32-bit, acquire and release variant on page C6-731 ARMv8.1 *)
    | "10  0  1  1  0  111" => ARM_ATOMIC ARM_LDUMIN 32 Rn Rs Rt (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL - 32-bit, acquire and release variant on page C6-737 ARMv8.1 *)
    | "10  0  1  1  1  000" => ARM_ATOMIC ARM_SWP 32 Rn Rs Rt (* SWP, SWPA, SWPAL, SWPL - 32-bit, acquire and release variant on page C6-945 ARMv8.1 *)
    | "11  0  0  0  0  000" => ARM_ATOMIC ARM_LDADD 64 Rn Rs Rt (* LDADD, LDADDA, LDADDAL, LDADDL - 64-bit, no memory ordering variant on page C6-636 ARMv8.1 *)
    | "11  0  0  0  0  001" => ARM_ATOMIC ARM_LDCLR 64 Rn Rs Rt (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 64-bit, no memory ordering variant on page C6-651 *)
    | "11  0  0  0  0  010" => ARM_ATOMIC ARM_LDEOR 64 Rn Rs Rt (* LDEOR, LDEORA, LDEORAL, LDEORL - 64-bit, no memory ordering variant on page C6-657 ARMv8.1 *)
    | "11  0  0  0  0  011" => ARM_ATOMIC ARM_LDSET 64 Rn Rs Rt (* LDSET, LDSETA, LDSETAL, LDSETL - 64-bit, no memory ordering variant on page C6-704 ARMv8.1 *)
    | "11  0  0  0  0  100" => ARM_ATOMIC ARM_LDSMAX 64 Rn Rs Rt (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL - 64-bit, no memory ordering variant on page C6-710 ARMv8.1 *)
    | "11  0  0  0  0  101" => ARM_ATOMIC ARM_LDSMIN 64 Rn Rs Rt (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL - 64-bit, no memory ordering variant on page C6-716 ARMv8.1 *)
    | "11  0  0  0  0  110" => ARM_ATOMIC ARM_LDUMAX 64 Rn Rs Rt (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL - 64-bit, no memory ordering variant on page C6-731 ARMv8.1 *)
    | "11  0  0  0  0  111" => ARM_ATOMIC ARM_LDUMIN 64 Rn Rs Rt (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL - 64-bit, no memory ordering variant on page C6-737 ARMv8.1 *)
    | "11  0  0  0  1  000" => ARM_ATOMIC ARM_SWP 64 Rn Rs Rt (* SWP, SWPA, SWPAL, SWPL - 64-bit, no memory ordering variant on page C6-945 ARMv8.1 *)
    | "11  0  0  1  0  000" => ARM_ATOMIC ARM_LDADD 64 Rn Rs Rt (* LDADD, LDADDA, LDADDAL, LDADDL - 64-bit, release variant on page C6-637 ARMv8.1 *)
    | "11  0  0  1  0  001" => ARM_ATOMIC ARM_LDCLR 64 Rn Rs Rt (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 64-bit, release variant on page C6-652 ARMv8.1 *)
    | "11  0  0  1  0  010" => ARM_ATOMIC ARM_LDEOR 64 Rn Rs Rt (* LDEOR, LDEORA, LDEORAL, LDEORL - 64-bit,release variant on page C6-658 ARMv8.1 *)
    | "11  0  0  1  0  011" => ARM_ATOMIC ARM_LDSET 64 Rn Rs Rt (* LDSET, LDSETA, LDSETAL, LDSETL - 64-bit,release variant on page C6-705 ARMv8.1 *)
    | "11  0  0  1  0  100" => ARM_ATOMIC ARM_LDSMAX 64 Rn Rs Rt (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL -64-bit, release variant on page C6-711 ARMv8.1 *)
    | "11  0  0  1  0  101" => ARM_ATOMIC ARM_LDSMIN 64 Rn Rs Rt (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL -64-bit, release variant on page C6-717 ARMv8.1 *)
    | "11  0  0  1  0  110" => ARM_ATOMIC ARM_LDUMAX 64 Rn Rs Rt (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL -64-bit, release variant on page C6-732 ARMv8.1 *)
    | "11  0  0  1  0  111" => ARM_ATOMIC ARM_LDUMIN 64 Rn Rs Rt (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL - 64-bit, release variant on page C6-738ARMv8.1 *)
    | "11  0  0  1  1  000" => ARM_ATOMIC ARM_SWP 64 Rn Rs Rt (* SWP, SWPA, SWPAL, SWPL - 64-bit, release variant on page C6-946 ARMv8.1 *)
    | "11  0  1  0  0  000" => ARM_ATOMIC ARM_LDADD 64 Rn Rs Rt (* LDADD, LDADDA, LDADDAL, LDADDL - 64-bit, acquire variant on page C6-636 ARMv8.1 *)
    | "11  0  1  0  0  001" => ARM_ATOMIC ARM_LDCLR 64 Rn Rs Rt (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 64-bit,acquire variant on page C6-651 ARMv8.1 *)
    | "11  0  1  0  0  010" => ARM_ATOMIC ARM_LDEOR 64 Rn Rs Rt (* LDEOR, LDEORA, LDEORAL, LDEORL - 64-bit, acquire variant on page C6-657 ARMv8.1 *)
    | "11  0  1  0  0  011" => ARM_ATOMIC ARM_LDSET 64 Rn Rs Rt (* LDSET, LDSETA, LDSETAL, LDSETL - 64-bit,acquire variant on page C6-704 ARMv8.1 *)
    | "11  0  1  0  0  100" => ARM_ATOMIC ARM_LDSMAX 64 Rn Rs Rt (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL -64-bit, acquire variant on page C6-710 ARMv8.1 *)
    | "11  0  1  0  0  101" => ARM_ATOMIC ARM_LDSMIN 64 Rn Rs Rt (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL -64-bit, acquire variant on page C6-716 ARMv8.1 *)
    | "11  0  1  0  0  110" => ARM_ATOMIC ARM_LDUMAX 64 Rn Rs Rt (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL -64-bit, acquire variant on page C6-731 ARMv8.1 *)
    | "11  0  1  0  0  111" => ARM_ATOMIC ARM_LDUMIN 64 Rn Rs Rt (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL - 64-bit, acquire variant on page C6-737 ARMv8.1 *)
    | "11  0  1  0  1  000" => ARM_ATOMIC ARM_SWP 64 Rn Rs Rt (* SWP, SWPA, SWPAL, SWPL - 64-bit, acquire varia *)
    | "11  0  1  0  1  100" => ARM_ATOMIC ARM_LDAPR 64 Rn Rs Rt (* LDAPR... *)
    | "1   0  1  1  0  000" => ARM_ATOMIC ARM_LDADD 64 Rn Rs Rt (* LDADD, LDADDA, LDADDAL, LDADDL - 64-bit,acquire and release variant on page C6-636 ARMv8.1 *)
    | "11  0  1  1  0  001" => ARM_ATOMIC ARM_LDCLR 64 Rn Rs Rt (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 64-bit,acquire and release variant on page C6-651 ARMv8.1 *)
    | "11  0  1  1  0  010" => ARM_ATOMIC ARM_LDEOR 64 Rn Rs Rt (* LDEOR, LDEORA, LDEORAL, LDEORL - 64-bit,acquire and release variant on page C6-657 ARMv8.1 *)
    | "11  0  1  1  0  011" => ARM_ATOMIC ARM_LDSET 64 Rn Rs Rt (* LDSET, LDSETA, LDSETAL, LDSETL - 64-bit,acquire and release variant on page C6-704 ARMv8.1 *)
    | "11  0  1  1  0  100" => ARM_ATOMIC ARM_LDSMAX 64 Rn Rs Rt (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL -64-bit, acquire and release variant on page C6-710 ARMv8.1 *)
    | "11  0  1  1  0  101" => ARM_ATOMIC ARM_LDSMIN 64 Rn Rs Rt (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL -64-bit, acquire and release variant on page C6-716 ARMv8.1 *)
    | "11  0  1  1  0  110" => ARM_ATOMIC ARM_LDUMAX 64 Rn Rs Rt (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL -64-bit, acquire and release variant on page C6-731 ARMv8.1 *)
    | "11  0  1  1  0  111" => ARM_ATOMIC ARM_LDUMIN 64 Rn Rs Rt (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL -64-bit, acquire and release variant on page C6-737 ARMv8.1 *)
    | "11  0  1  1  1  000" => ARM_ATOMIC ARM_SWP 64 Rn Rs Rt (* SWP, SWPA, SWPAL, SWPL - 64-bit, acquire and release variant on page C6-945 *)
    else UDF end.


  (* exttype - 3bit encoding of the type of extension. See J1-7387 and 7388 *)
  (* Assign the extended value ro regt *)
  Definition ExtendReg regt (w regn exttype shift:N) :=
    let exttype := <{exttype#3}> in
    let signed  := <{exttype [2]}> in
    <{if 4#3 < (shift#3) then exn 0 else nop end;
      temp[200] := lcast w X[regn];
      if exttype = 0#3 then (* UXTB *) temp[201] := ucast 8  Xtemp[200] else
      if exttype = 1#3 then (* UXTH *) temp[201] := ucast 16 Xtemp[200] else
      if exttype = 2#3 then (* UXTW *) temp[201] := ucast 32 Xtemp[200] else
      if exttype = 3#3 then (* UXTX *) temp[201] := ucast 64 Xtemp[200] else
      if exttype = 4#3 then (* SXTB *) temp[201] := scast 8  Xtemp[200] else
      if exttype = 5#3 then (* SXTH *) temp[201] := scast 16 Xtemp[200] else
      if exttype = 6#3 then (* SXTW *) temp[201] := scast 32 Xtemp[200] else
                            (* SXTX *) temp[201] := scast 64 Xtemp[200]
      end end end end end end end;
      regt := Xtemp[201]
    }>.

  Definition arm_ldr_reg2il (Xn Xm Xt extend size S:N) :=
    let scale := Word size 64 in
    let shift := match S with | 0 => 0 | _ => size end in
    let datasize := N.shiftl 8 size in
    let dbytes := N.shiftl 1 size in
    let calc_offset := ExtendReg (temp[9000]) 64 Xm extend shift in
    let undefined := <{extend#3 & 2#3 = 0#3}> in <{
      if undefined then exn 0 else nop end;
      calc_offset ;
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + Xtemp[9000]);
      store[Xtemp[1000],X[Xt],dbytes]
    }>.

  Definition arm_str_reg2il (Xn Xm Xt extend size S:N) :=
    let scale := Word size 64 in
    let shift := match S with | 0 => 0 | _ => size end in
    let datasize := N.shiftl 8 size in
    let dbytes := N.shiftl 1 size in
    let calc_offset := ExtendReg (temp[9000]) 64 Xm extend shift in
    let undefined := <{extend#3 & 2#3 = 0#3}> in <{
      if undefined then exn 0 else nop end;
      calc_offset ;
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + Xtemp[9000]);
      temp[2000] := load[Xtemp[1000],LittleE,dbytes];
      var[Xt] := ucast 64 Xtemp[2000]
    }>.

  Definition arm_ldrb_reg2il (Xn Xm Xt extend:N) :=
    let calc_offset := ExtendReg (temp[9000]) 64 Xm extend 0 in
    let undefined := <{extend#3 & 2#3 = 0#3}> in <{
      if undefined then exn 0 else nop end;
      calc_offset;
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + Xtemp[9000]);
      var[Xt] := load[Xtemp[1000],1]
    }>.

  Definition arm_ldrsb_reg2il (Xn Xm Xt size extend:N) :=
    let calc_offset := ExtendReg (temp[9000]) 64 Xm extend 0 in
    let undefined := <{extend#3 & 2#3 = 0#3}> in <{
      if undefined then exn 0 else nop end;
      calc_offset;
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + Xtemp[9000]);
      var[Xt] := ucast 64 (scast size load[Xtemp[1000],1])
    }>.

  Definition arm_ldrh_reg2il (Xn Xm Xt extend S:N) :=
    let calc_offset := ExtendReg (temp[9000]) 64 Xm extend S in
    let undefined := <{extend#3 & 2#3 = 0#3}> in <{
      if undefined then exn 0 else nop end;
      calc_offset;
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + Xtemp[9000]);
      var[Xt] := ucast 64 load[Xtemp[1000],2]
    }>.

  Definition arm_ldrsh_reg2il (Xn Xm Xt extend size S:N) :=
    let calc_offset := ExtendReg (temp[9000]) 64 Xm extend S in
    let undefined := <{extend#3 & 2#3 = 0#3}> in <{
      if undefined then exn 0 else nop end;
      calc_offset;
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + Xtemp[9000]);
      var[Xt] := ucast 64 (scast size load[Xtemp[1000],2])
    }>.

  Definition arm_ldrsw_reg2il (Xn Xm Xt extend S:N) :=
    let shift := match S with 0 => 0 | _ => 2 end in
    let calc_offset := ExtendReg (temp[9000]) 64 Xm extend S in
    let undefined := <{extend#3 & 2#3 = 0#3}> in <{
      if undefined then exn 0 else nop end;
      calc_offset;
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + Xtemp[9000]);
      var[Xt] := scast 64 load[Xtemp[1000],4]
    }>.

  Definition arm_strb_reg2il (Xn Xm Xt extend:N) :=
    let calc_offset := ExtendReg (temp[9000]) 64 Xm extend 0 in
    let undefined := <{extend#3 & 2#3 = 0#3}> in <{
      if undefined then exn 0 else nop end;
      calc_offset;
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + Xtemp[9000]);
      store[Xtemp[1000],X[Xt],1]
    }>.

  Definition arm_strh_reg2il (Xn Xm Xt extend S:N) :=
    let calc_offset := ExtendReg (temp[9000]) 64 Xm extend S in
    let undefined := <{extend#3 & 2#3 = 0#3}> in <{
      if undefined then exn 0 else nop end;
      calc_offset;
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      (temp[1000] := Xtemp[1000] + Xtemp[9000]);
      store[Xtemp[1000],X[Xt],2]
    }>.

  (*register offset*)
  Definition load_store_reg_off  :=
    let opc := n.[22,24] in
    let size := n.[30,32] in
    let v_ := n.[26] in
    let option_ := n.[13,16] in
    let Rt := n.[0,5] in
    let Rn := n.[5,10] in
    let Rm := n.[16,21] in
    let S := n.[12] in
    match[bits] size, v_, opc, option_ with
    | "-   -  -   x0x  " => UDF (* Unallocated. *)
    | "x1  1  1x  -    " => UDF (* Unallocated. *)
    | "00  0  00  !=011" => ARM_LD_STR_REG ARM_STRB_REG Rn Rm Rt option_ size S(* STRB (register) - Extended register variant on page C6-877 *)
    | "00  0  00  011  " => ARM_LD_STR_REG ARM_STRB_REG Rn Rm Rt option_ size S(* STRB (register) - Shifted register variant on page C6-877 *)
    | "00  0  01  !=011" => ARM_LD_STR_REG ARM_LDRB_REG Rn Rm Rt option_ size S(* LDRB (register) - Extended register variant on page C6-679 *)
    | "00  0  01  011  " => ARM_LD_STR_REG ARM_LDRB_REG Rn Rm Rt option_ size S(* LDRB (register) - Shifted register variant on page C6-679 *)
    | "00  0  10  !=011" => ARM_LD_STR_REG ARM_LDRSB_REG Rn Rm Rt option_ 64 S(* LDRSB (register) - 64-bit with extended register offset variant on page C6-688 *)
    | "00  0  10  011  " => ARM_LD_STR_REG ARM_LDRSB_REG Rn Rm Rt option_ 64 S(* LDRSB (register) - 64-bit with shifted register offset variant on page C6-688 *)
    | "00  0  11  !=011" => ARM_LD_STR_REG ARM_LDRSB_REG Rn Rm Rt option_ 32 S(* LDRSB (register) - 32-bit with extended register offset variant on page C6-688 *)
    | "00  0  11  011  " => ARM_LD_STR_REG ARM_LDRSB_REG Rn Rm Rt option_ 32 S(* LDRSB (register) - 32-bit with shifted register offset variant on page C6-688 *)
    | "00  1  00  !=011" => UDF (* STR (register, SIMD&FP) *)
    | "00  1  00  011  " => UDF (* STR (register, SIMD&FP) *)
    | "00  1  01  !=011" => UDF (* LDR (register, SIMD&FP) *)
    | "00  1  01  011  " => UDF (* LDR (register, SIMD&FP) *)
    | "00  1  10  -    " => UDF (* STR (register, SIMD&FP) *)
    | "00  1  11  -    " => UDF (* LDR (register, SIMD&FP) *)
    | "01  0  00  -    " => ARM_LD_STR_REG ARM_STRH_REG Rn Rm Rt option_ size S (* STRH (register) *)
    | "01  0  01  -    " => ARM_LD_STR_REG ARM_LDRH_REG Rn Rm Rt option_ size S (* LDRH (register) *) (*TODO: Check this*)
    | "01  0  10  -    " => ARM_LD_STR_REG ARM_LDRSH_REG Rn Rm Rt option_ 64 S (* LDRSH (register) - 64-bit variant on page C6-693 *)
    | "01  0  11  -    " => ARM_LD_STR_REG ARM_LDRSH_REG Rn Rm Rt option_ 64 S (* LDRSH (register) - 32-bit variant on page C6-693 *)
    | "01  1  00  -    " => UDF (* STR (register, SIMD&FP) *)
    | "01  1  01  -    " => UDF (* LDR (register, SIMD&FP) *)
    | "1x  0  11  -    " => UDF (* Unallocated. *)
    | "1x  1  1x  -    " => UDF (* Unallocated. *)
    | "10  0  00  -    " => ARM_LD_STR_REG ARM_STR_REG Rn Rm Rt option_ 2 S (* STR (register) - 32-bit variant on page C6-873 *)
    | "10  0  01  -    " => ARM_LD_STR_REG ARM_LDR_REG Rn Rm Rt option_ 2 S (* LDR (register) - 32-bit variant on page C6-675 *)
    | "10  0  10  -    " => ARM_LD_STR_REG ARM_LDRSW_REG Rn Rm Rt option_ size S (* LDRSW (register) *)
    | "10  1  00  -    " => UDF (* STR (register, SIMD&FP) *)
    | "10  1  01  -    " => UDF (* LDR (register, SIMD&FP) *)
    | "11  0  00  -    " => ARM_LD_STR_REG ARM_STR_REG Rn Rm Rt option_ 3 S (* STR (register) - 64-bit variant on page C6-873 *)
    | "11  0  01  -    " => ARM_LD_STR_REG ARM_LDR_REG Rn Rm Rt option_ 3 S (* LDR (register) - 64-bit variant on page C6-675 *)
    | "11  0  10  -    " => ARM_LD_STR_REG ARM_PRFM_REG Rn Rm Rt option_ size S (* PRFM (register) *)
    | "11  1  00  -    " => UDF (* STR (register, SIMD&FP) *)
    | "11  1  01  -    " => UDF (* LDR (register, SIMD&FP) *)
    else UDF end.


  Definition arm_ldraa2il_constr (Xn Xt S imm9:N) (wback wbunknown wbsuppress:bool) :=
    let offset := <{scast 64 (S#1++imm9#9)}> in
    let wbunknown := b2exp wbunknown in
    let wbsuppress := b2exp wbsuppress in
    let wback := b2exp wback in
    <{
      if (Xn # 5) = (31 # 5) then CheckSPAlignment else nop end; temp[1000] := X[Xn];
      temp[1000] := Xtemp[1000] + offset;
      var[Xt] := load[Xtemp[1000],8];
      if wback & !wbsuppress then
        temp[1001] := Xtemp[1000];
        if wbunknown then temp[1001] := unknown 64 else nop end;
        var[Xn] := Xtemp[1001]
      else
        nop
      end
    }>.

  Definition arm_ldraa2il (Xn Xt S imm9:N) (wback:bool) :=
    let wback' := wback in
    let wback := b2exp wback in
    let constraint_check := <{ wback & (Xt#5 = Xn#5) & (Xn#5 <> 31#5) }> in <{
      if ! constraint_check then {arm_ldraa2il_constr Xn Xt S imm9 wback' false false} else
      (* Constraint_NOP *)
      if unknown 1 then nop else
      (* Constraint_UNDEF *)
      if unknown 1 then havoc else
      (* Constraint_UNKNOWN *)
      if unknown 1 then {arm_ldraa2il_constr Xn Xt S imm9 wback' true false} else
      (* Constraint_WBSUPPRESS *)
      {arm_ldraa2il_constr Xn Xt S imm9 wback' false true}
      end end end end
    }>.

(*pac*)
  Definition load_store_reg_pac :=
    let size := n.[30,32] in
    let v_ := n.[26] in
    let m_ := n.[23] in
    let w_ := n.[11] in
    let Rt := n.[0,5] in
    let Rn := n.[5,10] in
    let imm9 := n.[12,21] in
    let s_ := n.[22] in
    match[bits] size, v_, m_, w_ with
    | "!=11  -  -  -" => UDF (* Unallocated. - *)
    | "11    0  0  0" => ARM_LDRAA Rn Rt s_ imm9 false (* LDRAA, LDRAB - Key A, offset variant on page C6-983 Armv8.3 *)
    | "11    0  0  1" => ARM_LDRAA Rn Rt s_ imm9 true (* LDRAA, LDRAB - Key A, pre-indexed variant on page C6-983 Armv8.3 *)
    | "11    0  1  0" => ARM_LDRAA Rn Rt s_ imm9 false (* LDRAA, LDRAB - Key B, offset variant on page C6-983 Armv8.3 *)
    | "11    0  1  1" => ARM_LDRAA Rn Rt s_ imm9 true (* LDRAA, LDRAB - Key B, pre-indexed variant on page C6-983 Armv8.3 *)
    | "11    1  -  -" => UDF (* Unallocated. *)
    else UDF end.

  (* The lifters for these and the *_IMM counterparts can be combined but
     we'd need to add logic for calculating the offset. Might be worth it
     to cut down on loc. *)
(*unsigned immediate*)
  Definition load_store_reg_u_imm  :=
    let opc := n.[22,24] in
    let size := n.[30,32] in
    let v_ := n.[26] in
    let Rt := n.[0,5] in
    let Rn := n.[5,10] in
    let imm12 := n.[10,22] in
    match[bits] size, v_, opc with
    | "x1  1  1x" => UDF (* Unallocated. *)
    | "00  0  00" => ARM_INDEXED ARM_STRB_IMM Rn Rt imm12 size false true true (* STRB (immediate) *)
    | "00  0  01" => ARM_INDEXED ARM_LDRB_IMM Rn Rt imm12 size false true true (* LDRB (immediate) *)
    | "00  0  10" => ARM_INDEXED ARM_LDRSB_IMM Rn Rt imm12 64 false true true (* LDRSB (immediate) - 64-bit variant on page C6-685 *)
    | "00  0  11" => ARM_INDEXED ARM_LDRSB_IMM Rn Rt imm12 32 false true true (* LDRSB (immediate) - 32-bit variant on page C6-685 *)
    | "00  1  00" => UDF (* STR (immediate, SIMD&FP) - 8-bit variant on page C7-1631 *)
    | "00  1  01" => UDF (* LDR (immediate, SIMD&FP) - 8-bit variant on page C7-1358 *)
    | "00  1  10" => UDF (* STR (immediate, SIMD&FP) - 128-bit variant on page C7-1631 *)
    | "00  1  11" => UDF (* LDR (immediate, SIMD&FP) - 128-bit variant on page C7-1358 *)
    | "01  0  00" => ARM_INDEXED ARM_STRH_IMM Rn Rt imm12 size false true true (* STRH (immediate) *)
    | "01  0  01" => ARM_INDEXED ARM_LDRH_IMM Rn Rt imm12 size false true true (* LDRH (immediate) *)
    | "01  0  10" => ARM_INDEXED ARM_LDRSH_IMM Rn Rt imm12 64 false true true (* LDRSH (immediate) - 64-bit variant on page C6-690 *)
    | "01  0  11" => ARM_INDEXED ARM_LDRSH_IMM Rn Rt imm12 32 false true true (* LDRSH (immediate) - 32-bit variant on page C6-690 *)
    | "01  1  00" => UDF (* STR (immediate, SIMD&FP) - 16-bit variant on page C7-1631 *)
    | "01  1  01" => UDF (* LDR (immediate, SIMD&FP) - 16-bit variant on page C7-1358 *)
    | "1x  0  11" => UDF (* Unallocated. *)
    | "1x  1  1x" => UDF (* Unallocated. *)
    | "10  0  00" => ARM_INDEXED ARM_STR_IMM Rn Rt imm12 32 false true true (* STR (immediate) - 32-bit variant on page C6-870 *)
    | "10  0  01" => ARM_INDEXED ARM_LDR_IMM Rn Rt imm12 32 false true true (* LDR (immediate) - 32-bit variant on page C6-670 *)
    | "10  0  10" => ARM_INDEXED ARM_LDRSW_IMM Rn Rt imm12 size false true true (* LDRSW (immediate) *)
    | "10  1  00" => UDF (* STR (immediate, SIMD&FP) - 32-bit variant on page C7-1631 *)
    | "10  1  01" => UDF (* LDR (immediate, SIMD&FP) - 32-bit variant on page C7-1358 *)
    | "11  0  00" => ARM_INDEXED ARM_STR_IMM Rn Rt imm12 64 false true true (* STR (immediate) - 64-bit variant on page C6-870 *)
    | "11  0  01" => ARM_INDEXED ARM_LDR_IMM Rn Rt imm12 64 false true true (* LDR (immediate) - 64-bit variant on page C6-670 *)
    | "11  0  10" => ARM_LOAD_GEN ARM_PRFM_IMM Rn Rt imm12 size (* PRFM (immediate) *)
    | "11  1  00" => UDF (* STR (immediate, SIMD&FP) - 64-bit variant on page C7-2115 *)
    | "11  1  01" => UDF (* LDR (immediate, SIMD&FP) - 64-bit variant on page C7-1801 *)
    else UDF end.

    (*Loads and Stores C4.1.4-266*)
    Definition load_store :=
    let op0 := n.[28,32] in
    let op1 := n.[26] in
    let op2 := n.[23,25] in
    let op3 := n.[16,22] in
    let op4 := n.[10,12] in
    match[bits] op0, op1, op2, op3, op4 with
  | "0x00  1  00  000000  - " => UDF (* Advanced SIMD load/store multiple structures on page C4-267 *)
  | "0x00  1  01  0xxxxx  - " => UDF (* Advanced SIMD load/store multiple structures (post-indexed) on page C4-268 *)
  | "0x00  1  0x  1xxxxx  - " => UDF (* Unallocated. *)
  | "0x00  1  10  x00000  - " => UDF (* Advanced SIMD load/store single structure on page C4-269 *)
  | "0x00  1  11  -       - " => UDF (* Advanced SIMD load/store single structure (post-indexed) on page C4-272 *)
  | "0x00  1  x0  x1xxxx  - " => UDF (* Unallocated. *)
  | "0x00  1  x0  xx1xxx  - " => UDF (* Unallocated. *)
  | "0x00  1  x0  xxx1xx  - " => UDF (* Unallocated. *)
  | "0x00  1  x0  xxxx1x  - " => UDF (* Unallocated. *)
  | "0x00  1  x0  xxxxx1  - " => UDF (* Unallocated. *)
  | "1101  0  1x  1xxxxx  - " => load_store_mem_tags (* Load/store memory tags on page C4-276 *)
  | "1x00  1  -   -       - " => UDF (* Unallocated. *)
  | "xx00  0  0x  -       - " => load_store_exclusive (* Load/store exclusive on page C4-276 *)
  | "xx01  0  1x  0xxxxx  00" => ldapr_stlr_imm_u (* LDAPR/STLR (unscaled immediate) on page C4-279 *)
  | "xx01  -  0x  -       - " => load_reg_literal (* Load register (literal) on page C4-280 *)
  | "xx10  -  00  -       - " => load_store_no_alloc_pair  (* Load/store no-allocate pair (offset) on page C4-280 *)
  | "xx10  -  01  -       - " => load_store_post_indx_pair (* Load/store register pair (post-indexed) on page C4-281 *)
  | "xx10  -  10  -       - " => load_store_pair_offset (* Load/store register pair (offset) on page C4-282 *)
  | "xx10  -  11  -       - " => load_store_pre_indx_pair (* Load/store register pair (pre-indexed) on page C4-282 *)
  | "xx11  -  0x  0xxxxx  00" => load_store_reg_imm_u(* Load/store register (unscaled immediate) on page C4-283 *)
  | "xx11  -  0x  0xxxxx  01" => load_store_reg_imm_poi (* Load/store register (immediate post-indexed) on page C4-284 *)
  | "xx11  -  0x  0xxxxx  10" => load_store_reg_unpriv (* Load/store register (unprivileged) on page C4-286 *)
  | "xx11  -  0x  0xxxxx  11" => load_store_reg_imm_pre  (* Load/store register (immediate pre-indexed) on page C4-286 *)
  | "xx11  -  0x  1xxxxx  00" => atomic (* Atomic memory operations on page C4-288 *)
  | "xx11  -  0x  1xxxxx  10" => load_store_reg_off (* Load/store register (register offset) on page C4-295 *)
  | "xx11  -  0x  1xxxxx  x1" => load_store_reg_pac (* Load/store register (pac) on page C4-297 *)
  | "xx11  -  1x  -       - " => load_store_reg_u_imm (* Load/store register (unsigned immediate) on page C4-297 *)
  else UDF end.

(** DP REG*)
  (*2 source dp*)
  Definition data_proc_2_src  :=
    let sf := n.[31] in
    let s_ := n.[29] in
    let opcode := n.[10,16] in
  match[bits] sf, s_, opcode with
    | "-  -  000001" => UDF (* Unallocated. - *)
    | "-  -  011xxx" => UDF (* Unallocated. - *)
    | "-  -  1xxxxx" => UDF (* Unallocated. - *)
    | "-  0  00011x" => UDF (* Unallocated. - *)
    | "-  0  001101" => UDF (* Unallocated. - *)
    | "-  0  00111x" => UDF (* Unallocated. - *)
    | "-  1  00001x" => UDF (* Unallocated. - *)
    | "-  1  0001xx" => UDF (* Unallocated. - *)
    | "-  1  001xxx" => UDF (* Unallocated. - *)
    | "-  1  01xxxx" => UDF (* Unallocated. - *)
    | "0  -  000000" => UDF (* Unallocated. - *)
    | "0  0  000010" => ARM_UDIV (* UDIV - 32-bit variant on page C6-1356 - *)
    | "0  0  000011" => ARM_SDIV (* SDIV - 32-bit variant on page C6-1174 - *)
    | "0  0  00010x" => UDF (* Unallocated. - *)
    | "0  0  001000" => ARM_LSLV (* LSLV - 32-bit variant on page C6-1077 - *)
    | "0  0  001001" => ARM_LSRV (* LSRV - 32-bit variant on page C6-1083 - *)
    | "0  0  001010" => ARM_ASRV (* ASRV - 32-bit variant on page C6-787 - *)
    | "0  0  001011" => ARM_RORV (* RORV - 32-bit variant on page C6-1161 - *)
    | "0  0  001100" => UDF (* Unallocated. - *)
    | "0  0  010x11" => UDF (* Unallocated. - *)
    | "0  0  010000" => ARM_CRC32B (* CRC32B, CRC32H, CRC32W, CRC32X - CRC32B variant on page C6-866 - *)
    | "0  0  010001" => ARM_CRC32B (* CRC32B, CRC32H, CRC32W, CRC32X - CRC32H variant on page C6-866 - *)
    | "0  0  010010" => ARM_CRC32B (* CRC32B, CRC32H, CRC32W, CRC32X - CRC32W variant on page C6-866 - *)
    | "0  0  010100" => ARM_CRC32CB (* CRC32CB, CRC32CH, CRC32CW, CRC32CX - CRC32CB variant on page C6-868 - *)
    | "0  0  010101" => ARM_CRC32CB (* CRC32CB, CRC32CH, CRC32CW, CRC32CX - CRC32CH variant on page C6-868 - *)
    | "0  0  010110" => ARM_CRC32CB (* CRC32CB, CRC32CH, CRC32CW, CRC32CX - CRC32CW variant on page C6-868 - *)
    | "1  0  000000" => ARM_SUBP (* SUBP Armv8.5 *)
    | "1  0  000010" => ARM_UDIV (* UDIV - 64-bit variant on page C6-1356 - *)
    | "1  0  000011" => ARM_SDIV (* SDIV - 64-bit variant on page C6-1174 - *)
    | "1  0  000100" => ARM_IRG (* IRG Armv8.5 *)
    | "1  0  000101" => ARM_GMI (* GMI Armv8.5 *)
    | "1  0  001000" => ARM_LSLV (* LSLV - 64-bit variant on page C6-1077 - *)
    | "1  0  001001" => ARM_LSRV (* LSRV - 64-bit variant on page C6-1083 - *)
    | "1  0  001010" => ARM_ASRV (* ASRV - 64-bit variant on page C6-787 - *)
    | "1  0  001011" => ARM_RORV (* RORV - 64-bit variant on page C6-1161 - *)
    | "1  0  001100" => ARM_PACGA (* PACGA Armv8.3 *)
    | "1  0  010xx0" => UDF (* Unallocated. - *)
    | "1  0  010x0x" => UDF (* Unallocated. - *)
    | "1  0  010011" => ARM_CRC32B (* CRC32B, CRC32H, CRC32W, CRC32X - CRC32X variant on page C6-866 - *)
    | "1  0  010111" => ARM_CRC32CB (* CRC32CB, CRC32CH, CRC32CW, CRC32CX - CRC32CX variant on page C6-868 - *)
    | "1  1  000000" => ARM_SUBPS (* SUBPS Armv8.5 *)
    else UDF end.


  (*1 source*)
  Definition data_proc_1_src  :=
    let sf := n.[31] in
    let s_ := n.[29] in
    let opcode := n.[10,16] in
    let opcode2 := n.[16,21] in
    let Rn := n.[5,10] in
    let Rd := n.[0,5] in
    match[bits] sf, s_, opcode2, opcode, Rn with
    | "-  -  -      1xxxxx  -    " => UDF (* Unallocated. - *)
    | "-  -  xxx1x  -       -    " => UDF (* Unallocated. - *)
    | "-  -  xx1xx  -       -    " => UDF (* Unallocated. - *)
    | "-  -  x1xxx  -       -    " => UDF (* Unallocated. - *)
    | "-  -  1xxxx  -       -    " => UDF (* Unallocated. - *)
    | "-  0  00000  00011x  -    " => UDF (* Unallocated. - *)
    | "-  0  00000  001xxx  -    " => UDF (* Unallocated. - *)
    | "-  0  00000  01xxxx  -    " => UDF (* Unallocated. - *)
    | "-  1  -      -       -    " => UDF (* Unallocated. - *)
    | "0  -  00001  -       -    " => UDF (* Unallocated. - *)
    | "0  0  00000  000000  -    " => ARM_BITOPS ARM_RBIT sf Rn Rd (* RBIT - 32-bit variant on page C6-1146 - *)
    | "0  0  00000  000001  -    " => ARM_BITOPS ARM_REV16 sf Rn Rd (* REV16 - 32-bit variant on page C6-1151 - *)
    | "0  0  00000  000010  -    " => ARM_BITOPS ARM_REV sf Rn Rd (* REV - 32-bit variant on page C6-1149 - *)
    | "0  0  00000  000011  -    " => UDF (* Unallocated. *)
    | "0  0  00000  000100  -    " => ARM_BITOPS ARM_CLZ sf Rn Rd(* CLZ - 32-bit variant on page C6-849 - *)
    | "0  0  00000  000101  -    " => ARM_BITOPS ARM_CLS sf Rn Rd(* CLS - 32-bit variant on page C6-848 - *)
    | "1  0  00000  000000  -    " => ARM_BITOPS ARM_RBIT sf Rn Rd(* RBIT - 64-bit variant on page C6-1146 - *)
    | "1  0  00000  000001  -    " => ARM_BITOPS ARM_REV16 sf Rn Rd(* REV16 - 64-bit variant on page C6-1151 - *)
    | "1  0  00000  000010  -    " => ARM_BITOPS ARM_REV32 sf Rn Rd(* REV32 - *)
    | "1  0  00000  000011  -    " => ARM_BITOPS ARM_REV sf Rn Rd(* REV - 64-bit variant on page C6-1149 - *)
    | "1  0  00000  000100  -    " => ARM_BITOPS ARM_CLZ sf Rn Rd(* CLZ - 64-bit variant on page C6-849 - *)
    | "1  0  00000  000101  -    " => ARM_BITOPS ARM_CLS sf Rn Rd(* CLS - 64-bit variant on page C6-848 - *)
    | "1  0  00001  000000  -    " => ARM_PACIA (* PACIA, PACIA1716, PACIASP, PACIAZ, PACIZA - PACIA variant on page C6-1132 Armv8.3 *)
    | "1  0  00001  000001  -    " => ARM_PACIB (* PACIB, PACIB1716, PACIBSP, PACIBZ, PACIZB - PACIB variant on page C6-1134 Armv8.3 *)
    | "1  0  00001  000010  -    " => ARM_PACDA (* PACDA, PACDZA - PACDA variant on page C6-1129 Armv8.3 *)
    | "1  0  00001  000011  -    " => ARM_PACDB (* PACDB, PACDZB - PACDB variant on page C6-1130 Armv8.3 *)
    | "1  0  00001  000100  -    " => ARM_AUTIA (* AUTIA, AUTIA1716, AUTIASP, AUTIAZ, AUTIZA - AUTIA variant on page C6-793 Armv8.3 *)
    | "1  0  00001  000101  -    " => ARM_AUTIB (* AUTIB, AUTIB1716, AUTIBSP, AUTIBZ, AUTIZB - AUTIB variant on page C6-795 Armv8.3 *)
    | "1  0  00001  000110  -    " => ARM_AUTDA (* AUTDA, AUTDZA - AUTDA variant on page C6-791 Armv8.3 *)
    | "1  0  00001  000111  -    " => ARM_AUTDB (* AUTDB, AUTDZB - AUTDB variant on page C6-792 Armv8.3 *)
    | "1  0  00001  001000  11111" => ARM_PACIA (* PACIA, PACIA1716, PACIASP, PACIAZ, PACIZA - PACIZA variant on page C6-1132 Armv8.3 *)
    | "1  0  00001  001001  11111" => ARM_PACIB (* PACIB, PACIB1716, PACIBSP, PACIBZ, PACIZB - PACIZB variant on page C6-1134 Armv8.3 *)
    | "1  0  00001  001010  11111" => ARM_PACDA (* PACDA, PACDZA - PACDZA variant on page C6-1129 Armv8.3 *)
    | "1  0  00001  001011  11111" => ARM_PACDB (* PACDB, PACDZB - PACDZB variant on page C6-1130 Armv8.3 *)
    | "1  0  00001  001100  11111" => ARM_AUTIA (* AUTIA, AUTIA1716, AUTIASP, AUTIAZ, AUTIZA - AUTIZA variant on page C6-793 Armv8.3 *)
    | "1  0  00001  001101  11111" => ARM_AUTIB (* AUTIB, AUTIB1716, AUTIBSP, AUTIBZ, AUTIZB - AUTIZB variant on page C6-795 Armv8.3 *)
    | "1  0  00001  001110  11111" => ARM_AUTDA (* AUTDA, AUTDZA - AUTDZA variant on page C6-791 Armv8.3 *)
    | "1  0  00001  001111  11111" => ARM_AUTDB (* AUTDB, AUTDZB - AUTDZB variant on page C6-792 Armv8.3 *)
    | "1  0  00001  010000  11111" => ARM_XPACD (* XPACD, XPACI, XPACLRI - XPACI variant on pageC6-1369 Armv8.3 *)
    | "1  0  00001  010001  11111" => ARM_XPACD (* XPACD, XPACI, XPACLRI - XPACD variant on pageC6-1369 Armv8.3 *)
    | "1  0  00001  01001x  -    " => UDF (* Unallocated. - *)
    | "1  0  00001  0101xx  -    " => UDF (* Unallocated. - *)
    | "1  0  00001  011xxx  -    " => UDF (* Unallocated. *)
    else UDF end.


  (*logical - shifted reg*)
  Definition data_proc_logical  :=
    let sf := n.[31] in
    let opc := n.[29,31] in
    let n_ := n.[21] in
    let imm6 := n.[10,16] in let shift := n.[22,24] in
    let Rn := n.[5,10] in let Rm := n.[16,21] in let Rd := n.[0,5] in
    match[bits] sf, opc, n_, imm6 with
    | "0  -   -  1xxxxx" => UDF (* Unallocated. *)
    | "0  00  0  -     " => ARM_LOG_SHIFTED ARM_AND_LOG_REG sf shift Rm imm6 Rn Rd(* AND (shifted register) - 32-bit variant on page C6-538 *)
    | "0  00  1  -     " => ARM_LOG_SHIFTED ARM_BIC_LOG_REG sf shift Rm imm6 Rn Rd(* BIC (shifted register) - 32-bit variant on page C6-556 *)
    | "0  01  0  -     " => ARM_LOG_SHIFTED ARM_ORR_LOG_REG sf shift Rm imm6 Rn Rd(* ORR (shifted register) - 32-bit variant on page C6-792 *)
    | "0  01  1  -     " => ARM_LOG_SHIFTED ARM_ORN_LOG_REG sf shift Rm imm6 Rn Rd(* ORN (shifted register) - 32-bit variant on page C6-788 *)
    | "0  10  0  -     " => ARM_LOG_SHIFTED ARM_EOR_LOG_REG sf shift Rm imm6 Rn Rd(* EOR (shifted register) - 32-bit variant on page C6-620 *)
    | "0  10  1  -     " => ARM_LOG_SHIFTED ARM_EON_LOG_REG sf shift Rm imm6 Rn Rd(* EON (shifted register) - 32-bit variant on page C6-617 *)
    | "0  11  0  -     " => ARM_LOG_SHIFTED ARM_ANDS_LOG_REG sf shift Rm imm6 Rn Rd (* ANDS (shifted register) - 32-bit variant on page C6-542 *)
    | "0  11  1  -     " => ARM_LOG_SHIFTED ARM_BICS_LOG_REG sf shift Rm imm6 Rn Rd (* BICS (shifted register) - 32-bit variant on page C6-558 *)
    | "1  00  0  -     " => ARM_LOG_SHIFTED ARM_AND_LOG_REG sf shift Rm imm6 Rn Rd(* AND (shifted register) - 64-bit variant on page C6-538 *)
    | "1  00  1  -     " => ARM_LOG_SHIFTED ARM_BIC_LOG_REG sf shift Rm imm6 Rn Rd(* BIC (shifted register) - 64-bit variant on page C6-556 *)
    | "1  01  0  -     " => ARM_LOG_SHIFTED ARM_ORR_LOG_REG sf shift Rm imm6 Rn Rd(* ORR (shifted register) - 64-bit variant on page C6-792 *)
    | "1  01  1  -     " => ARM_LOG_SHIFTED ARM_ORN_LOG_REG sf shift Rm imm6 Rn Rd(* ORN (shifted register) - 64-bit variant on page C6-788 *)
    | "1  10  0  -     " => ARM_LOG_SHIFTED ARM_EOR_LOG_REG sf shift Rm imm6 Rn Rd(* EOR (shifted register) - 64-bit variant on page C6-620 *)
    | "1  10  1  -     " => ARM_LOG_SHIFTED ARM_EON_LOG_REG sf shift Rm imm6 Rn Rd(* EON (shifted register) - 64-bit variant on page C6-617 *)
    | "1  11  0  -     " => ARM_LOG_SHIFTED ARM_ANDS_LOG_REG sf shift Rm imm6 Rn Rd(* ANDS (shifted register) - 64-bit variant on page C6-542 *)
    | "1  11  1  -     " => ARM_LOG_SHIFTED ARM_BICS_LOG_REG sf shift Rm imm6 Rn Rd(* BICS (shifted register) - 64-bit variant on page C6-558 *)
    else UDF end.


  (*add/sub - shifted reg*)
  Definition add_sub_shifted  :=
    let sf := n.[31] in
    let opc := n.[30] in
    let s := n.[29] in
    let shift := n.[22,24] in
    let imm6 := n.[10,16] in
    let Rm := n.[16,21] in let Rn := n.[5,10] in let Rd := n.[0,5] in
    match[bits] sf, opc, s, shift, imm6 with
    | "-  -  -  11  -     " => UDF (* Unallocated. *)
    | "0  -  -  -   1xxxxx" => UDF (* Unallocated. *)
    | "0  0  0  -   -     " => ARM_DATA_SHIFTED ARM_ADD_SHIFTED_REG sf s shift Rm imm6 Rn Rd  (* ADD (shifted register) - 32-bit variant on page C6-527 *)
    | "0  0  1  -   -     " => ARM_DATA_SHIFTED ARM_ADDS_SHIFTED_REG sf s shift Rm imm6 Rn Rd  (* ADDS (shifted register) - 32-bit variant on page C6-533 *)
    | "0  1  0  -   -     " => ARM_DATA_SHIFTED ARM_SUB_SHIFTED_REG sf s shift Rm imm6 Rn Rd  (* SUB (shifted register) - 32-bit variant on page C6-932 *)
    | "0  1  1  -   -     " => ARM_DATA_SHIFTED ARM_SUBS_SHIFTED_REG sf s shift Rm imm6 Rn Rd  (* SUBS (shifted register) - 32-bit variant on page C6-938 *)
    | "1  0  0  -   -     " => ARM_DATA_SHIFTED ARM_ADD_SHIFTED_REG sf s shift Rm imm6 Rn Rd  (* ADD (shifted register) - 64-bit variant on page C6-527 *)
    | "1  0  1  -   -     " => ARM_DATA_SHIFTED ARM_ADDS_SHIFTED_REG sf s shift Rm imm6 Rn Rd  (* ADDS (shifted register) - 64-bit variant on page C6-533 *)
    | "1  1  0  -   -     " => ARM_DATA_SHIFTED ARM_SUB_SHIFTED_REG sf s shift Rm imm6 Rn Rd  (* SUB (shifted register) - 64-bit variant on page C6-932 *)
    | "1  1  1  -   -     " => ARM_DATA_SHIFTED ARM_SUBS_SHIFTED_REG sf s shift Rm imm6 Rn Rd (* SUBS (shifted register) - 64-bit variant on page C6-938 *)
    else UDF end.

  (*add/sub - extended reg*)
  Definition add_sub_extended  :=
    let sf := n.[31] in
    let op := n.[30] in
    let s := n.[29] in
    let opt := n.[22,24] in
    let imm3 := n.[10,13] in
    let Rn := n.[5,10] in let Rd:= n.[0,5] in
    let option_ := n.[13,16] in
    let Rm := n.[16,21] in
    match[bits] sf, op, s, opt, imm3 with
    | "-  -  -  -   1x1" => UDF (* Unallocated. *)
    | "-  -  -  -   11x" => UDF (* Unallocated. *)
    | "-  -  -  x1  -  " => UDF (* Unallocated. *)
    | "-  -  -  1x  -  " => UDF (* Unallocated. *)
    | "0  0  0  00  -  " => ARM_EXTENDED ARM_ADD_EXTENDED_REG sf s opt Rm option_ imm3 Rn Rd(* ADD (extended register) - 32-bit variant on page C6-523 *)
    | "0  0  1  00  -  " => ARM_EXTENDED ARM_ADDS_EXTENDED_REG sf s opt Rm option_ imm3 Rn Rd(* ADDS (extended register) - 32-bit variant on page C6-529 *)
    | "0  1  0  00  -  " => ARM_EXTENDED ARM_SUB_EXTENDED_REG sf s opt Rm option_ imm3 Rn Rd(* SUB (extended register) - 32-bit variant on page C6-928 *)
    | "0  1  1  00  -  " => ARM_EXTENDED ARM_SUBS_EXTENDED_REG sf s opt Rm option_ imm3 Rn Rd(* SUBS (extended register) - 32-bit variant on page C6-934 *)
    | "1  0  0  00  -  " => ARM_EXTENDED ARM_ADD_EXTENDED_REG sf s opt Rm option_ imm3 Rn Rd(* ADD (extended register) - 64-bit variant on page C6-523 *)
    | "1  0  1  00  -  " => ARM_EXTENDED ARM_ADDS_EXTENDED_REG sf s opt Rm option_ imm3 Rn Rd(* ADDS (extended register) - 64-bit variant on page C6-529 *)
    | "1  1  0  00  -  " => ARM_EXTENDED ARM_SUB_EXTENDED_REG sf s opt Rm option_ imm3 Rn Rd(* SUB (extended register) - 64-bit variant on page C6-928 *)
    | "1  1  1  00  -  " => ARM_EXTENDED ARM_SUBS_EXTENDED_REG sf s opt Rm option_ imm3 Rn Rd(* SUBS (extended register) - 64-bit variant on page C6-934 *)
    else UDF end.

  (*add/sub - with carry*)
  Definition add_sub_carry  :=
    let sf := n.[31] in
    let op := n.[30] in
    let s := n.[29] in
    let Rm := n.[16,21] in let Rn := n.[5,10] in let Rd := n.[0,5] in
    match[bits] sf, op, s with
      | "0  0  0" => ARM_CARRY ARM_ADC sf s Rm Rn Rd(* ADC - 32-bit variant on page C6-754 *)
      | "0  0  1" => ARM_CARRY ARM_ADCS sf s Rm Rn Rd(* ADCS - 32-bit variant on page C6-756 *)
      | "0  1  0" => ARM_CARRY ARM_SBC sf s Rm Rn Rd(* SBC - 32-bit variant on page C6-1164 *)
      | "0  1  1" => ARM_CARRY ARM_SBCS sf s Rm Rn Rd(* SBCS - 32-bit variant on page C6-1166 *)
      | "1  0  0" => ARM_CARRY ARM_ADC sf s Rm Rn Rd(* ADC - 64-bit variant on page C6-754 *)
      | "1  0  1" => ARM_CARRY ARM_ADCS sf s Rm Rn Rd(* ADCS - 64-bit variant on page C6-756 *)
      | "1  1  0" => ARM_CARRY ARM_SBC sf s Rm Rn Rd(* SBC - 64-bit variant on page C6-1164 *)
      | "1  1  1" => ARM_CARRY ARM_SBCS sf s Rm Rn Rd(* SBCS - 64-bit variant on page C6-1166 *)
      else UDF end.

  (*rotate right into flags*)
  Definition rotate  :=
    let sf := n.[31] in
    let op := n.[30] in
    let s_ := n.[29] in
    let o2 := n.[4] in
    match[bits] sf, op, s_, o2 with
    | "0  -  -  -" => UDF (* Unallocated. - *)
    | "1  0  0  -" => UDF (* Unallocated. - *)
    | "1  0  1  0" => ARM_RMIF (* RMIF Armv8.4 *)
    | "1  0  1  1" => UDF (* Unallocated. - *)
    | "1  1  -  -" => UDF (* Unallocated. - *)
    else UDF end.

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
    | "0  0  0  -         -  -  -     " => UDF (* Unallocated. - *)
    | "0  0  1  !=000000  -  -  -     " => UDF (* Unallocated. - *)
    | "0  0  1  000000    -  0  !=1101" => UDF (* Unallocated. - *)
    | "0  0  1  000000    -  1  -     " => UDF (* Unallocated. - *)
    | "0  0  1  000000    0  0  1101  " => ARM_SETF8 (* SETF8, SETF16 - SETF8 variant on page C6-1175 Armv8.4 *)
    | "0  0  1  000000    1  0  1101  " => ARM_SETF8 (* SETF8, SETF16 - SETF16 variant on page C6-1175 Armv8.4 *)
    | "0  1  -  -         -  -  -     " => UDF (* Unallocated. - *)
    | "1  -  -  -         -  -  -     " => UDF (* Unallocated. *)
    else UDF end.

  (*TODO:conditional compare immediate*)
  Definition cond_compare_imm :=
    let sf := n.[31] in
    let op := n.[30] in
    let s_ := n.[29] in
    let o2 := n.[10] in
    let o3 := n.[4] in
    let Rn := n.[5,10] in
    let cond := n.[12,16] in
    let imm := n.[16,21] in
    let nzcv := n.[0,4] in
    match[bits] sf, op, s_, o2, o3 with
    | "-  -  -  -  1" => UDF (* Unallocated. *)
    | "-  -  -  1  -" => UDF (* Unallocated. *)
    | "-  -  0  -  -" => UDF (* Unallocated. *)
    | "0  0  1  0  0" => ARM_CCMN_IMM sf Rn imm nzcv cond(* CCMN (immediate) - 32-bit variant on page C6-833 *)
    | "0  1  1  0  0" => ARM_CCMP_IMM sf Rn imm nzcv cond(* CCMP (immediate) - 32-bit variant on page C6-837 *)
    | "1  0  1  0  0" => ARM_CCMN_IMM sf Rn imm nzcv cond(* CCMN (immediate) - 64-bit variant on page C6-833 *)
    | "1  1  1  0  0" => ARM_CCMP_IMM sf Rn imm nzcv cond(* CCMP (immediate) - 64-bit variant on page C6-837 *)
    else UDF end.

  (*conditional compare immediate*)
  Definition cond_compare_reg :=
    let sf := n.[31] in
    let op := n.[30] in
    let s_ := n.[29] in
    let o2 := n.[10] in
    let o3 := n.[4] in
    let Rm := n.[16,21] in let Rn := n.[5,10]
    in let cond := n.[12,16] in let nzcv := n.[0,4] in
    match[bits] sf, op, s_, o2, o3 with
  | "-  -  -  -  1" => UDF (* Unallocated. *)
  | "-  -  -  1  -" => UDF (* Unallocated. *)
  | "-  -  0  -  -" => UDF (* Unallocated. *)
  | "0  0  1  0  0" => ARM_CCMN_REG sf Rm cond Rn nzcv(* CCMN (register) - 32-bit variant on page C6-835 *)
  | "0  1  1  0  0" => ARM_CCMP_REG sf Rm cond Rn nzcv(* CCMP (register) - 32-bit variant on page C6-839 *)
  | "1  0  1  0  0" => ARM_CCMN_REG sf Rm cond Rn nzcv(* CCMN (register) - 64-bit variant on page C6-835 *)
  | "1  1  1  0  0" => ARM_CCMP_REG sf Rm cond Rn nzcv(* CCMP (register) - 64-bit variant on page C6-839 *)
  else UDF end.

  (*conditional select*)
  Definition cond_select :=
    let sf := n.[31] in
    let op := n.[30] in
    let s_ := n.[29] in
    let op2 := n.[10,12] in
    match[bits] sf, op, s_, op2 with
    | "-  -  -  1x" => UDF (* Unallocated. *)
    | "-  -  1  - " => UDF (* Unallocated. *)
    | "0  0  0  00" => ARM_CSEL (* CSEL - 32-bit variant on page C6-871 *)
    | "0  0  0  01" => ARM_CSINC (* CSINC - 32-bit variant on page C6-877 *)
    | "0  1  0  00" => ARM_CSINV (* CSINV - 32-bit variant on page C6-879 *)
    | "0  1  0  01" => ARM_CSNEG (* CSNEG - 32-bit variant on page C6-881 *)
    | "1  0  0  00" => ARM_CSEL (* CSEL - 64-bit variant on page C6-871 *)
    | "1  0  0  01" => ARM_CSINC (* CSINC - 64-bit variant on page C6-877 *)
    | "1  1  0  00" => ARM_CSINV (* CSINV - 64-bit variant on page C6-879 *)
    | "1  1  0  01" => ARM_CSNEG (* CSNEG - 64-bit variant on page C6-881 *)
    else UDF end.

  (*3 source dp*)
  Definition data_proc_3_src  :=
    let sf := n.[31] in
    let op54 := n.[29,31] in
    let op31 := n.[21,24] in
    let o0 := n.[15] in
    match[bits] sf, op54, op31, o0 with
    | "-  00  010  1" => UDF (* Unallocated. *)
    | "-  00  011  -" => UDF (* Unallocated. *)
    | "-  00  100  -" => UDF (* Unallocated. *)
    | "-  00  110  1" => UDF (* Unallocated. *)
    | "-  00  111  -" => UDF (* Unallocated. *)
    | "-  01  -    -" => UDF (* Unallocated. *)
    | "-  1x  -    -" => UDF (* Unallocated. *)
    | "0  00  000  0" => ARM_MADD (* MADD - 32-bit variant on page C6-1085 *)
    | "0  00  000  1" => ARM_MSUB (* MSUB - 32-bit variant on page C6-1109 *)
    | "0  00  001  0" => UDF (* Unallocated. *)
    | "0  00  001  1" => UDF (* Unallocated. *)
    | "0  00  010  0" => UDF (* Unallocated. *)
    | "0  00  101  0" => UDF (* Unallocated. *)
    | "0  00  101  1" => UDF (* Unallocated. *)
    | "0  00  110  0" => UDF (* Unallocated. *)
    | "1  00  000  0" => ARM_MADD (* MADD - 64-bit variant on page C6-1085 *)
    | "1  00  000  1" => ARM_MSUB (* MSUB - 64-bit variant on page C6-1109 *)
    | "1  00  001  0" => ARM_SMADDL (* SMADDL *)
    | "1  00  001  1" => ARM_SMSUBL (* SMSUBL *)
    | "1  00  010  0" => ARM_SMULH (* SMULH *)
    | "1  00  101  0" => ARM_UMADDL (* UMADDL *)
    | "1  00  101  1" => ARM_UMSUBL (* UMSUBL *)
    | "1  00  110  0" => ARM_UMULH (* UMULH *)
    else UDF end.

  Definition dp_reg :=
    let op0 := n.[30] in
    let op1 := n.[28] in
    let op2 := n.[21,25] in
    let op3 := n.[10,16] in
    match[bits] op0, op1, op2, op3 with
  | "0  1  0110  -     " => data_proc_2_src (* Data-processing (2 source) *)
  | "1  1  0110  -     " => data_proc_1_src (* Data-processing (1 source) on page C4-301 *)
  | "-  0  0xxx  -     " => data_proc_logical (* Logical (shifted register) on page C4-303 *)
  | "-  0  1xx0  -     " => add_sub_shifted (* Add/subtract (shifted register) on page C4-303 *)
  | "-  0  1xx1  -     " => add_sub_extended (* Add/subtract (extended register) on page C4-304 *)
  | "-  1  0000  000000" => add_sub_carry (* Add/subtract (with carry) on page C4-305 *)
  | "-  1  0000  x00001" => rotate (* Rotate right into flags on page C4-305 *)
  | "-  1  0000  xx0010" => evaluate (* Evaluate into flags on page C4-306 *)
  | "-  1  0010  xxxx0x" => cond_compare_reg (* Conditional compare (register) on page C4-306 *)
  | "-  1  0010  xxxx1x" => cond_compare_imm (* Conditional compare (immediate) on page C4-307 *)
  | "-  1  0100  -     " => cond_select (* Conditional select on page C4-307 *)
  | "-  1  1xxx  -     " => data_proc_3_src (* Data-processing (3 source) on page C4-308 *)
  else UDF end.

  Definition dp_fp_simd := UDF.

  Definition Pack_NZCV (n z c v : exp) : exp :=
  (* Shift each flag into its proper architectural position *)
  let n_shifted := BinOp OP_LSHIFT (Cast CAST_UNSIGNED 4 n) (Word 3 4) in
  let z_shifted := BinOp OP_LSHIFT (Cast CAST_UNSIGNED 4 z) (Word 2 4) in
  let c_shifted := BinOp OP_LSHIFT (Cast CAST_UNSIGNED 4 c) (Word 1 4) in

  (* Merge all positions together into one expression using bitwise OR *)
  BinOp OP_OR (BinOp OP_OR n_shifted z_shifted) (BinOp OP_OR c_shifted (Cast CAST_UNSIGNED 4 v)).

  (*Shared Functions for Shift, Extend, AddWCarry*)
  Definition AddWithCarry datasize x y carry_in:=
    let unsigned_sum := BinOp OP_PLUS (BinOp OP_PLUS x y) (Cast CAST_UNSIGNED datasize carry_in) in
    let signed_sum := BinOp OP_PLUS (BinOp OP_PLUS x y) (Cast CAST_SIGNED datasize carry_in) in
    let result := unsigned_sum in
    let n := Cast CAST_HIGH 1 result in
    let z :=  (UnOp OP_NOT (BinOp OP_EQ (Word 0 datasize) result)) in
    let c := BinOp OP_OR (BinOp OP_LT result x) (BinOp OP_AND (BinOp OP_EQ (Word (N.ones datasize) datasize) result) carry_in) in
    let v := BinOp OP_OR
            (BinOp OP_SLT
            (BinOp OP_AND (BinOp OP_XOR x result)(BinOp OP_XOR y result))(Word 0 datasize))
            (BinOp OP_AND (BinOp OP_EQ (Word (N.ones datasize) datasize) result) carry_in) in

    let nzcv := Pack_NZCV n z c v in
    (result, nzcv).

  (*Not doing UDIV because we might need floating values?*)
  (*Definition RoundTowardsZero x := x.*)


  (*shift type*)
  Variant armsrtype :=
  | ARM_LSL | ARM_LSR | ARM_ASR | ARM_ROR.

  Variant ExtendType :=
  | ExtendType_SXTB | ExtendType_SXTH | ExtendType_SXTW | ExtendType_SXTX | ExtendType_UXTB
  | ExtendType_UXTH | ExtendType_UXTW | ExtendType_UXTX.


  Definition DecodeRegExtend op :=
  match op with
  | 0 => ExtendType_UXTB
  | 1 => ExtendType_UXTH
  | 2 => ExtendType_UXTW
  | 3 => ExtendType_UXTX
  | 4 => ExtendType_SXTB
  | 5 => ExtendType_SXTH
  | 6 => ExtendType_SXTW
  | _ => ExtendType_SXTX
  end.


  Variant arm_data_r_inst :=
  | ARM_ADD_SHIFTED_REG_V
  | ARM_ADDS_SHIFTED_REG_V
  | ARM_SUB_SHIFTED_REG_V
  | ARM_SUBS_SHIFTED_REG_V
  | ARM_AND_LOG_REG_V
  | ARM_ANDS_LOG_REG_V | ARM_BIC_LOG_REG_V | ARM_BICS_LOG_REG_V | ARM_ORR_LOG_REG_V | ARM_ORN_LOG_REG_V | ARM_EOR_LOG_REG_V | ARM_EON_LOG_REG_V
  | ARM_ADC_V  | ARM_ADCS_V | ARM_SBC_V  | ARM_SBCS_V | ARM_ADD_EXTENDED_REG_V  | ARM_ADDS_EXTENDED_REG_V | ARM_SUB_EXTENDED_REG_V
  | ARM_SUBS_EXTENDED_REG_V | ARM_CCMN_REG_V | ARM_CCMP_REG_V
  .

  (*returns signed/unsigned extended value*)
  Definition ExtendReg2 reg exttype shift datasize:=
  let (unsigned, len) := match exttype with
  | ExtendType_SXTB => (false, 8)
  | ExtendType_SXTH => (false, 16)
  | ExtendType_SXTW => (false, 32)
  | ExtendType_SXTX => (false, 64)
  | ExtendType_UXTB => (true, 8)
  | ExtendType_UXTH => (true, 16)
  | ExtendType_UXTW => (true, 32)
  | ExtendType_UXTX => (true, 64)
  end in
  let min := N.min len (datasize-shift) in
  let cast := if unsigned then CAST_UNSIGNED else CAST_SIGNED in
  let slice := Extract (min - 1) 0 (R[ reg , datasize ]) in  (* X reg N: read reg as an N-bit register value *)
  BinOp OP_LSHIFT (Cast cast datasize slice) (Word shift datasize).

  Definition ShiftC value shiftype amount datasize:=
  let result :=
  match shiftype with
  | ARM_LSL =>  BinOp OP_LSHIFT value amount
  | ARM_LSR =>  BinOp OP_RSHIFT value amount
  | ARM_ASR =>  BinOp OP_ARSHIFT value amount
  | ARM_ROR => let x := BinOp OP_RSHIFT value amount in
               let y := BinOp OP_LSHIFT value (BinOp OP_MINUS (Word datasize datasize) amount) in
               BinOp OP_OR x y
  end in
  Ite (BinOp OP_EQ amount (Word 0 datasize)) value result.

  Definition ShiftReg reg shiftype amount datasize :=
  let value := R[ reg ,datasize ] in
  ShiftC value shiftype amount datasize.

  Definition DecodeShift op :=
  match op with
  | 0 => ARM_LSL
  | 1 => ARM_LSR
  | 2 => ARM_ASR
  | _ => ARM_ROR
  end.

  Definition arm_data_il (assign assign_flags:bool) (Rn:N) (result flags: exp):=
  let assign_check := if assign then arm_assign_R Rn result else Nop in
  let assign_flag := if assign_flags then arm_assign_flags flags else assign_check in
  assign_flag.

  (*Returns an exp*)
  Definition arm_data_r_shiftc (sf s shift Rm:N) imm6 (Rn Rd:N) (assign assign_flags: bool) (op:exp -> exp -> exp) :=
  let datasize := if sf =? 1 then 64 else 32 in
  let shift_type := DecodeShift shift in
  match (sf, (N.testbit imm6 5)) with
  |(0, true) => Nop
  | _ => let operand2 := ShiftReg Rm shift_type (Word imm6 datasize) datasize in
         let operand1 := R[ Rn , datasize] in
  let result := op operand1 operand2 in
  let result64 := if sf =? 1 then result else Cast CAST_UNSIGNED 64 result in
  arm_data_il assign assign_flags Rn result64 (Unknown datasize)
  end.

  (*op : the actual AddWithCarry
  instr : for ANDS and BICS*)
  Definition arm_data_r_addwithcarry (cond sf s shift Rm:N) imm6 (Rn:N) (assign assign_flag:bool) (op:exp -> exp -> exp->exp*exp) :=
  let datasize := if sf =? 1 then 64 else 32 in
  let shift_type := DecodeShift shift in
  match (sf, (N.testbit imm6 5)) with
  |(0, true) => Nop
  |(3,_) => Nop
  | _ =>  let operand2 := ShiftReg Rm shift_type (Word imm6 datasize) datasize in
          let operand1 := R[ Rn , datasize] in
  let (result, nzcv) := op operand1 operand2 (Unknown datasize) in
  (*assign=assign to register, assign_flag=set flag values*)
  let result64 := if sf =? 1 then result else Cast CAST_UNSIGNED 64 result in
  arm_data_il assign assign_flag Rn result64 nzcv
  end.

  (*only for arith functions, this is the "addwcarry"*)
  Definition arm_data_r_extended (cond sf s Rm:N) option_ imm3 Rn Rd (assign assign_flag:bool) (op: exp -> exp -> exp->exp*exp) :=
  let datasize := if sf =? 1 then 64 else 32 in
  let extend_type := DecodeRegExtend option_ in
  if 4 <? imm3 then (Exn 4) else (*Undefined*)
  let (operand1,reg_n) := if Rn=? 31 then ((SP_read datasize),32) else ((R[ Rn , datasize]),Rd) in
  let operand2 := ExtendReg2 Rm extend_type imm3 datasize in
  let (result,nzcv) := op operand1 operand2 (Unknown datasize)in
  (*operand1 is the thing to set.*)
  let result64 := if sf =? 1 then result else Cast CAST_UNSIGNED 64 result in
  arm_data_il assign assign_flag reg_n result64 nzcv.

  Definition arm_data_rev_il op sf Rd:=
  let datasize := if sf =? 1 then 64 else 32 in
  match op with
  | ARM_RBIT |ARM_REV |ARM_CLZ |ARM_CLS => arm_assign_R Rd (Unknown datasize)
  | ARM_REV16 => arm_assign_R Rd (Unknown 16)
  | ARM_REV32 => arm_assign_R Rd (Unknown 32)
  | ARM_REV64 => arm_assign_R Rd (Unknown 64)
  end.

  (*asrv, lsrv, etc.*)
  Definition arm_data_r_shift_il (sf Rm op2 Rn Rd:N) (assign assign_flags: bool) :=
  let datasize := if sf =? 1 then 64 else 32 in
  let shift_type := DecodeShift op2 in
  let operand2 := R[ Rm , datasize] in
  let result := ShiftReg Rn shift_type (BinOp OP_MOD operand2 (Word datasize datasize)) datasize in
  let result64 := if sf =? 1 then result else Cast CAST_UNSIGNED 64 result in
  arm_data_il assign assign_flags Rd result64 (Unknown datasize)
  .

  Definition arm_data_r_with_carry (sf Rm Rn Rd:N) (assign assign_flags: bool) (op: exp -> exp -> exp->exp*exp):=
  let datasize := if sf =? 1 then 64 else 32 in
  let operand2 := R[ Rm , datasize] in
  let operand1 := R[ Rn, datasize ] in
  let (result,_) := op operand1 operand2 (Word 0 1) in
  let result64 := if sf =? 1 then result else Cast CAST_UNSIGNED 64 result in
  arm_data_il assign assign_flags Rd result64 (Unknown datasize)
  .

  Definition arm_data_r_with_cond (op:arm_data_r_inst) (cond sf Rm Rn nzcv:N):=
  let datasize := if sf =? 1 then 64 else 32 in
  let operand2 := R[ Rm , datasize] in
  let operand1 := R[ Rn, datasize ] in
  let (result, flags):= match op with
    | ARM_CCMN_REG_V =>  (AddWithCarry datasize operand1 operand2 (Word 0 1) )
    | _(*ARM_CCMP_REG_V*) =>  (AddWithCarry datasize operand1 (UnOp OP_NOT operand2) (Word 1 1))
    end in
  let nzcv_final := Ite (ConditionHolds cond) flags (Word nzcv 4) in
  (*if condition holds, nzcv final is the new flags from AddWithCarry else its just the value we read in*)
  let result64 := if sf =? 1 then result else Cast CAST_UNSIGNED 64 result in
  arm_data_il false true Rn result64 nzcv_final
  .

  Definition arm_datashft_reg2il op (cond sf s shift Rm Rd:N) imm6 (Rn:N):=
    let datasize := if sf =? 1 then 64 else 32 in
    let arm_addwithcarry := arm_data_r_addwithcarry cond sf s shift Rm imm6 Rn in
    match op with
    | ARM_ADD_SHIFTED_REG => arm_addwithcarry true false (fun a b _ => AddWithCarry datasize a b (Word 0 1))
    | ARM_ADDS_SHIFTED_REG => arm_addwithcarry true true (fun a b _ => AddWithCarry datasize a b (Word 0 1))
    | ARM_SUB_SHIFTED_REG => arm_addwithcarry true false (fun a b _ => AddWithCarry datasize a (UnOp OP_NOT b) (Word 1 1))
    | ARM_SUBS_SHIFTED_REG => arm_addwithcarry true true (fun a b _=> AddWithCarry datasize a (UnOp OP_NOT b) (Word 1 1))
    end.

  Definition arm_logshft_reg2il op (cond sf s shift Rm Rd:N) imm6 (Rn:N):=
    let arm_shiftc := arm_data_r_shiftc sf s shift Rm imm6 Rn Rd in
    match op with
    | ARM_AND_LOG_REG => arm_shiftc true false (fun a b => BinOp OP_AND a b)
    | ARM_ANDS_LOG_REG |ARM_TST_LOG_REG => arm_shiftc true true (fun a b => BinOp OP_AND a b)
    | ARM_BIC_LOG_REG => arm_shiftc true false (fun a b => BinOp OP_AND a (UnOp OP_NOT b))
    | ARM_BICS_LOG_REG => arm_shiftc true false (fun a b => BinOp OP_AND a (UnOp OP_NOT b))
    | ARM_ORR_LOG_REG |ARM_MOV_LOG_REG=> arm_shiftc true false (fun a b => BinOp OP_OR a b)
    | ARM_ORN_LOG_REG |ARM_MVN_LOG_REG  => arm_shiftc true false (fun a b => BinOp OP_OR a (UnOp OP_NOT b))
    | ARM_EOR_LOG_REG => arm_shiftc true false (fun a b => BinOp OP_XOR a b) (*TODO: EORS?*)
    | ARM_EON_LOG_REG => arm_shiftc true false (fun a b => BinOp OP_XOR a (UnOp OP_NOT b))
  
    end.

  Definition arm_withcarry_2il op (sf Rm Rn Rd:N) :=
    (*assign function here -> completed in the op_il function*)
    let datasize := if sf =? 1 then 64 else 32 in
    let arm_addwithcarry := arm_data_r_with_carry sf Rm Rn Rd in
    match op with 
    | ARM_ADC => arm_addwithcarry true false (fun a b _ => AddWithCarry datasize a b (Var R_CY))
    | ARM_ADCS => arm_addwithcarry true true (fun a b _ => AddWithCarry datasize a b (Var R_CY))
    | ARM_SBC => arm_addwithcarry true false (fun a b _ => AddWithCarry datasize a (UnOp OP_NOT b) (Var R_CY))
    | ARM_SBCS => arm_addwithcarry true true (fun a b _ => AddWithCarry datasize a (UnOp OP_NOT b) (Var R_CY))
    end.   

(**  Definition arm_data_r_il_shft op (cond sf s shift Rm Rd:N) imm6 (Rn:N) :=
    let arm_addwithcarry := arm_data_r_addwithcarry cond sf s shift Rm imm6 Rn in
    let arm_shiftc := arm_data_r_shiftc sf s shift Rm imm6 Rn Rd in
    arm_data_op_il op arm_shiftc arm_addwithcarry.*)

  Definition arm_extend_reg2il op (cond sf s Rm:N) option_ imm3 Rn Rd :=
    let datasize := if sf =? 1 then 64 else 32 in
    let arm_addwithcarry := arm_data_r_extended cond sf s Rm option_ imm3 Rn Rd in
    match op with
    | ARM_ADD_EXTENDED_REG => arm_addwithcarry true false (fun a b _ => AddWithCarry datasize a b (Word 0 1))
    | ARM_ADDS_EXTENDED_REG => arm_addwithcarry true true (fun a b _ => AddWithCarry datasize a b (Word 0 1))
    | ARM_SUB_EXTENDED_REG => arm_addwithcarry true false (fun a b _ => AddWithCarry datasize a (UnOp OP_NOT b) (Word 1 1))
    | ARM_SUBS_EXTENDED_REG => arm_addwithcarry true true (fun a b _=> AddWithCarry datasize a (UnOp OP_NOT b) (Word 1 1))
    end.



(**  Definition arm_data_r_il_carry op (sf Rm Rn Rd:N) :=
    (*assign function here -> completed in the op_il function*)
    let arm_addwithcarry := arm_data_r_with_carry sf Rm Rn Rd in
    let dummy_shiftc (asgn set_flags : bool) (operation : exp -> exp -> exp) : stmt := Nop in
    arm_data_op_il op dummy_shiftc arm_addwithcarry.*)

  (*SUBP/S: only for 64 bit*)
  Definition arm_subp_to_il (op Xn Xm Xd:N) (flag:bool ):stmt:=
    let operand1 := if Xn=?31 then (SP_read 64) else R[Xn, 64] in
    let operand2 := if Xm=?31 then (SP_read 64) else R[Xn, 64] in
    let op1_55 := Cast CAST_LOW 56 operand1 in
    let op2_55 := Cast CAST_LOW 56 operand2 in
    let op1_ext := Cast CAST_SIGNED 64 op1_55 in
    let op2_ext := Cast CAST_SIGNED 64 op2_55 in
    let (result,flags) := AddWithCarry 64 op1_ext op2_ext (Word 1 1) in
    arm_data_il true flag Xd result flags.

    (*Immediate*)
    Definition arm_data_i_addwithcarry (datasize sf s sh imm12 Rn Rd:N) (assign assign_flag:bool) (op:exp -> exp -> exp->exp*exp) :=
    let imm_ext := match sh with
    | 0 => Cast CAST_UNSIGNED datasize (Word imm12 datasize)
    | _ => BinOp OP_LSHIFT (Cast CAST_UNSIGNED datasize (Word imm12 datasize)) (Word 12 datasize)
    end in
    let operand1 := if Rn=?31 then (SP_read datasize) else R[Rn, datasize] in
    let (result, nzcv) := op operand1 imm_ext (Unknown datasize) in
    (*assign=assign to register, assign_flag=set flag values*)
    let result64 := if sf =? 1 then result else Cast CAST_UNSIGNED 64 result in
    arm_data_il assign assign_flag Rd result64 nzcv
    .

  Definition arm_data_i_with_cond op (sf Rn imm nzcv cond:N) :=
    let datasize := if sf =? 1 then 64 else 32 in
    let imm_ext := Cast CAST_UNSIGNED datasize (Word imm datasize) in
    let operand1 := R[ Rn, datasize ] in
    let (result, flags):= match op with
      | ARM_CCMN_IMM _ _ _ _ _=>  (AddWithCarry datasize operand1 imm_ext (Word 0 1) )
      | _(*ARM_CCMP_REG_V*) =>  (AddWithCarry datasize operand1 (UnOp OP_NOT imm_ext) (Word 1 1))
      end in
    let nzcv_final := Ite (ConditionHolds cond) flags (Word nzcv 4) in
    (*if condition holds, nzcv final is the new flags from AddWithCarry else its just the value we read in*)
    let result64 := if sf =? 1 then result else Cast CAST_UNSIGNED 64 result in
    arm_data_il false true Rn result64 nzcv_final.
  
  Definition arm_data_imm2il op sf s sh imm12 Rn Rd:=
  let datasize := if sf =? 1 then 64 else 32 in
  match op with
  | ARM_ADD_IMM => arm_data_i_addwithcarry datasize sf s sh imm12 Rn Rd true false (fun a b _ => AddWithCarry datasize a b (Word 0 1))
  | ARM_ADDS_IMM => arm_data_i_addwithcarry datasize sf s sh imm12 Rn Rd true true (fun a b _ => AddWithCarry datasize a b (Word 0 1))
  | ARM_SUB_IMM => arm_data_i_addwithcarry datasize sf s sh imm12 Rn Rd true false (fun a b _ => AddWithCarry datasize a (UnOp OP_NOT b) (Word 1 1))
  | ARM_SUBS_IMM => arm_data_i_addwithcarry datasize sf s sh imm12 Rn Rd true true (fun a b _ => AddWithCarry datasize a (UnOp OP_NOT b) (Word 1 1))
  end.

  Definition arm_log_imm2il op Rn Rd immr imms sf n_:=
  match op with
  | ARM_AND_IMM => arm_and_imm2il Rn Rd immr imms sf n_
  | ARM_ANDS_IMM => arm_ands_imm2il Rn Rd immr imms sf n_
  | ARM_EOR_IMM => arm_eor_imm2il Rn Rd immr imms sf n_
  | ARM_ORR_IMM => arm_orr_imm2il Rn Rd immr imms sf n_
  | ARM_BFM_IMM  => arm_bfm_imm2il Rn Rd immr imms sf n_
  | ARM_SBFM_IMM  => arm_sbfm_imm2il Rn Rd immr imms sf n_
  | ARM_UBFM_IMM => arm_ubfm_imm2il Rn Rd immr imms sf n_
  end.

  Definition arm_mov_imm2il op Rd imm16 size shift :=
  match op with 
  | ARM_MOVZ_IMM  => arm_movz_imm2il Rd imm16 size shift
  | ARM_MOVN_IMM  => arm_movn_imm2il Rd imm16 size shift
  | ARM_MOVK_IMM  => arm_movk_imm2il Rd imm16 size shift
  end.

  Definition arm_decode :=
    let op0 := n.[25,29] in
    match[bits] op0 with
    | "0000" => UDF (* Reserved *)
    | "0001" => UDF (* Unallocated. *)
    | "0010" => UDF (* SVE Instructions. See SVE on page A2-92 *)
    | "0011" => UDF (* Unallocated. *)
    | "100x" => dp_imm (* Data Processing -- Immediate *)
    | "101x" => branch_exc (* Branches, Exception Generating and System instructions on page C4-257 *)
    | "x1x0" => load_store (* Loads and Stores on page C4-266 *)
    | "x101" => dp_reg (* Data Processing -- Register on page C4-299 *)
    | "x111" => dp_fp_simd (* Data Processing -- Scalar Floating-Point and Advanced SIMD on page C4-309 *)
    else UDF end.

  (*final arm2il-C6.2.5*)
  Definition arm2il (a:addr) inst:=
  let il := match inst with
  (*DP imm*)
  | ARM_DATA_IMM op sf s sh imm12 Rn Rd => arm_data_imm2il op sf s sh imm12 Rn Rd
  (*logical imm*)
  | ARM_LOGICAL_IMM op Rn Rd immr imms sf n_ => arm_log_imm2il op Rn Rd immr imms sf n_
  (*move wide*)
  | ARM_MOVE_IMM op Rd imm16 size shift => arm_mov_imm2il op Rd imm16 size shift
  (*PC relative addressing*)
(*| ARM_ADRP_IMM
  | ARM_ADR_IMM *)
  (*compare immediate*)
  | ARM_CCMN_IMM sf Rn imm nzcv cond => arm_data_i_with_cond (ARM_CCMN_IMM sf Rn imm nzcv cond) sf Rn imm nzcv cond
  | ARM_CCMP_IMM sf Rn imm nzcv cond => arm_data_i_with_cond (ARM_CCMP_IMM sf Rn imm nzcv cond) sf Rn imm nzcv cond
  (*DP reg*)
  (*arith extended*)
  | ARM_EXTENDED op sf s opt Rm option_ imm3 Rn Rd => arm_extend_reg2il op 0 sf s Rm option_ imm3 Rn Rd
  (*arith shifted*)
  | ARM_DATA_SHIFTED op sf s shift Rm imm6 Rn Rd => arm_datashft_reg2il op 0 sf s shift Rm Rd imm6 Rn
  (*logical shifted*)
  | ARM_LOG_SHIFTED op sf shift Rm imm6 Rn Rd => arm_logshft_reg2il op 0 sf 0 shift Rm Rd imm6 Rn
  (*carry operations*)
  | ARM_CARRY op sf s Rm Rn Rd=> arm_withcarry_2il op sf Rm Rn Rd
  (*shift register*)
  | ARM_SHIFT _ sf Rm op2 Rn Rd => arm_data_r_shift_il sf Rm op2 Rn Rd true false
  (*conditional comparison*)
  | ARM_CCMN_REG sf Rm cond Rn nzcv=> arm_data_r_with_cond ARM_CCMN_REG_V cond sf Rm Rn nzcv
  | ARM_CCMP_REG sf Rm cond Rn nzcv=> arm_data_r_with_cond ARM_CCMP_REG_V cond sf Rm Rn nzcv
  (*rev*)
  | ARM_BITOPS op sf Rn Rd => arm_data_rev_il op sf Rd
  (*branch*)
  | ARM_B_COND cond imm19 => arm_b_cond2il cond imm19
  (*unconditional branch(register)*)
  | ARM_BR Xn => arm_br2il Xn
  | ARM_BLR Xn => arm_blr2il Xn
  | ARM_RET Xn => arm_ret2il Xn
  (*unconditional branch(imm)*)
  | ARM_B imm26 => arm_b2il imm26
  | ARM_BL imm26 => arm_bl2il imm26
  (*compare and branch(imm)*)
  | ARM_CBZ Rt imm19 size => arm_cbz2il Rt imm19 size
  | ARM_CBNZ Rt imm19 size => arm_cbnz2il Rt imm19 size
  (*test and branch(imm)*)
  | ARM_TBZ Rt imm14 b5 b40 => arm_tbz2il Rt imm14 b5 b40
  | ARM_TBNZ Rt imm14 b5 b40 => arm_tbnz2il Rt imm14 b5 b40
(*Loads and Stores*)
  (*exclusive/others*)
  | ARM_EXCLUSIVE ARM_STXRB size Xn Xs Xt Xt2 => arm_stxrb2il Xn Xs Xt
  | ARM_EXCLUSIVE ARM_STLXRB size Xn Xs Xt Xt2 => arm_stlxrb2il Xn Xs Xt
  | ARM_EXCLUSIVE ARM_LDXRB size Xn Xs Xt Xt2 => arm_ldxrb2il Xn Xt 
  | ARM_EXCLUSIVE ARM_LDXRH size Xn Xs Xt Xt2 => arm_ldxrh2il Xn Xt 
  | ARM_EXCLUSIVE ARM_LDAXRH size Xn Xs Xt Xt2 => arm_ldaxrh2il Xn Xt
  | ARM_EXCLUSIVE ARM_LDAXRB size Xn Xs Xt Xt2 => arm_ldaxrb2il Xn Xt
  | ARM_EXCLUSIVE ARM_STLLRB size Xn Xs Xt Xt2 => arm_stllrb2il Xn Xt
  | ARM_EXCLUSIVE ARM_STLLRH size Xn Xs Xt Xt2 => arm_stllrh2il Xn Xt
  | ARM_EXCLUSIVE ARM_STLRH size Xn Xs Xt Xt2 => arm_stlrh2il Xn Xt
  | ARM_EXCLUSIVE ARM_STLRB size Xn Xs Xt Xt2 => arm_stlrb2il Xn Xt
  | ARM_EXCLUSIVE ARM_STXRH size Xn Xs Xt Xt2 => arm_stxrh2il Xn Xs Xt
  | ARM_EXCLUSIVE ARM_STLXRH size Xn Xs Xt Xt2 => arm_stlxrh2il Xn Xs Xt
  | ARM_EXCLUSIVE ARM_LDLARB size Xn Xs Xt Xt2 => arm_ldlarb2il Xn Xt
  | ARM_EXCLUSIVE ARM_LDARB size Xn Xs Xt Xt2 => arm_ldarb2il Xn Xt
  | ARM_EXCLUSIVE ARM_LDARH size Xn Xs Xt Xt2 => arm_ldarh2il Xn Xt
  | ARM_EXCLUSIVE ARM_LDLARH size Xn Xs Xt Xt2 => arm_ldlarh2il Xn Xt
  | ARM_EXCLUSIVE ARM_STXR size Xn Xs Xt Xt2 => arm_stxr2il size Xn Xs Xt 
  | ARM_EXCLUSIVE ARM_STLXR size Xn Xs Xt Xt2 => arm_stxr2il_size size Xn Xs Xt
  | ARM_EXCLUSIVE ARM_STXP size Xn Xs Xt Xt2 => arm_stxp2il size Xn Xs Xt Xt2
  | ARM_EXCLUSIVE ARM_STLXP size Xn Xs Xt Xt2 => arm_stlxp2il size Xn Xs Xt Xt2 
  | ARM_EXCLUSIVE ARM_LDXR size Xn Xs Xt Xt2 => arm_ldxr2il size Xn Xt
  | ARM_EXCLUSIVE ARM_LDAXR size Xn Xs Xt Xt2 => arm_ldaxr2il size Xn Xt
  | ARM_EXCLUSIVE ARM_LDXP size Xn Xs Xt Xt2 => arm_ldxp2il size Xn Xt Xt2
  | ARM_EXCLUSIVE ARM_LDAXP size Xn Xs Xt Xt2 => havoc
  | ARM_EXCLUSIVE ARM_STLLR size Xn Xs Xt Xt2 => arm_stllr2il size Xn Xt
  | ARM_EXCLUSIVE ARM_STLR size Xn Xs Xt Xt2 => arm_stlr2il size Xn Xt
  | ARM_EXCLUSIVE ARM_LDLAR size Xn Xs Xt Xt2 => arm_ldlar2il size Xn Xt
  | ARM_EXCLUSIVE ARM_LDAR size Xn Xs Xt Xt2 => arm_ldar2il size Xn Xt
  (*bunch of variants for these, refer to page C4-230*)
  | ARM_EXCLUSIVE ARM_CASP size Xn Xs Xt Xt2 => arm_casp2il Xn Xs Xt size
  | ARM_EXCLUSIVE ARM_CASB size Xn Xs Xt Xt2 => arm_casb2il Xn Xs Xt
  | ARM_EXCLUSIVE ARM_CASH size Xn Xs Xt Xt2 => arm_cash2il Xn Xs Xt
  | ARM_EXCLUSIVE ARM_CAS size Xn Xs Xt Xt2 => arm_cas2il Xn Xs Xt size
  (*LDAPR/STLR unscaled immediate*)
  | ARM_LOAD_GEN ARM_STLURB Xn Xt imm9 size => arm_stlurb2il Xn Xt imm9
  | ARM_LOAD_GEN ARM_LDAPURB Xn Xt imm9 size => arm_ldapurb2il Xn Xt (Word imm9 64)
  | ARM_LOAD_GEN ARM_LDAPURSB Xn Xt imm9 size => arm_ldapursb2il Xn Xt (Word imm9 64) size
  | ARM_LOAD_GEN ARM_STLURH Xn Xt imm9 size => arm_stlurh2il Xn Xt (Word imm9 64) 
  | ARM_LOAD_GEN ARM_LDAPURH Xn Xt imm9 size => arm_ldapurh2il Xn Xt (Word imm9 64)
  | ARM_LOAD_GEN ARM_LDAPURSH Xn Xt imm9 size => arm_ldapursh2il Xn Xt (Word imm9 64) size
  | ARM_LOAD_GEN ARM_LDAPUR Xn Xt imm9 size => arm_ldapur2il Xn Xt (Word imm9 64) size
  | ARM_LOAD_GEN ARM_LDAPURSW Xn Xt imm9 size => arm_ldapursw2il Xn Xt (Word imm9 64) size
  | ARM_LOAD_GEN ARM_STLUR Xn Xt imm9 size => arm_stlur2il Xn Xt (Word imm9 64) size
  | ARM_LOAD_GEN ARM_PRFM Xn Xt imm9 size => arm_prfm_lit2il Xt imm9
  | ARM_LOAD_GEN ARM_PRFM_IMM Xn Xt imm9 size => havoc
  | ARM_ATOMIC ARM_LDAPRB size Xn Xs Xt => arm_ldaprb2il Xn Xt
  | ARM_ATOMIC ARM_LDAPRH size Xn Xs Xt => arm_ldaprh2il Xn Xt
  | ARM_ATOMIC ARM_LDAPR size Xn Xs Xt => arm_ldapr2il size Xn Xt
  (*load/store memory tags*)
  | ARM_STG Xn Xt imm9 writeback printindex => arm_stg2il Xn Xt imm9 writeback printindex
  | ARM_STZG Xn Xt imm9 writeback printindex => arm_stzg2il Xn Xt imm9 writeback printindex
  | ARM_STZGM Xn Xt => arm_stzgm2il Xt Xn         
  | ARM_LDG Xn Xt imm9 => arm_ldg2il Xn Xt imm9
  | ARM_ST2G Xn Xt imm9 writeback printindex => arm_st2g2il Xn Xt imm9 writeback printindex
  | ARM_STGM Xn Xt => arm_stgm2il Xn Xt
  | ARM_STZ2G Xn Xt imm9 writeback printindex => arm_stz2g2il Xn Xt imm9 writeback printindex
  | ARM_LDGM Xn Xt => arm_ldgm2il Xn Xt
  (*load register (literal)*)
  | ARM_LD_REG_LIT ARM_LDR_LIT Xt imm19 size => arm_ldr_lit2il Xt imm19 size
  | ARM_LD_REG_LIT ARM_LDRSW_LIT Xt imm19 size => arm_ldrsw_lit2il Xt imm19
  | ARM_LD_REG_LIT ARM_PRFM_LIT Xt imm19 size => arm_prfm_lit2il Xt imm19
  (*load/store no-allocate pair (offset)*)
  | ARM_STNP Xn Xt Xt2 imm7 scale => arm_stnp2il Xn Xt Xt2 imm7 scale 
  | ARM_LDNP Xn Xt Xt2 imm7 scale => arm_stnp2il Xn Xt Xt2 imm7 scale 
  (*load/store register pair (post-indexed, pre-indexed, offset)*)
  | ARM_LD_STR_REG_PAIR ARM_STP Xn Xt Xt2 imm7 scale wback postindex => arm_stp2il Xn Xt Xt2 imm7 scale wback postindex 
  | ARM_LD_STR_REG_PAIR ARM_LDP Xn Xt Xt2 imm7 scale wback postindex => arm_ldp2il Xn Xt Xt2 imm7 scale wback postindex 
  | ARM_LD_STR_REG_PAIR ARM_LDPSW Xn Xt Xt2 imm7 scale wback postindex => arm_ldpsw2il Xn Xt Xt2 imm7 wback postindex 
  | ARM_LD_STR_REG_PAIR ARM_STGP Xn Xt Xt2 imm7 scale wback postindex => arm_stgp2il Xn Xt Xt2 imm7 wback postindex 
  (*load/store register (unscaled immediate)*)
  | ARM_LOAD_GEN ARM_STURB Xn Xt imm9 _ => arm_sturb2il Xn Xt imm9
  | ARM_LOAD_GEN ARM_LDURB Xn Xt imm9 _ => arm_ldurb2il Xn Xt imm9
  | ARM_LOAD_GEN ARM_LDURSB Xn Xt imm9 size => arm_ldursb2il Xn Xt imm9 size
  | ARM_LOAD_GEN ARM_STURH Xn Xt imm9 _ => arm_sturh2il Xn Xt imm9
  | ARM_LOAD_GEN ARM_LDURH Xn Xt imm9 _ => arm_ldurh2il Xn Xt imm9
  | ARM_LOAD_GEN ARM_LDURSH Xn Xt imm9 size => arm_ldursh2il Xn Xt imm9 size
  | ARM_LOAD_GEN ARM_STUR Xn Xt imm9 size => arm_stur2il Xn Xt imm9 size
  | ARM_LOAD_GEN ARM_LDUR Xn Xt imm9 size => arm_ldur2il Xn Xt imm9 size
  | ARM_LOAD_GEN ARM_LDURSW Xn Xt imm9 _ => arm_ldursw2il Xn Xt imm9
  (*imm pre/post-indexed*)
  | ARM_INDEXED ARM_STRB_IMM Xn Xt imm912 size signed wback postindex => arm_strb_imm2il Xn Xt imm912 signed wback postindex
  | ARM_INDEXED ARM_LDRB_IMM Xn Xt imm912 size signed wback postindex => arm_ldrb_imm2il Xn Xt imm912 signed wback postindex 
  | ARM_INDEXED ARM_LDRSB_IMM Xn Xt imm912 size signed wback postindex => arm_ldrsb_imm2il Xn Xt imm912 size signed wback postindex
  | ARM_INDEXED ARM_LDR_IMM Xn Xt imm912 size signed wback postindex => arm_ldr_imm2il Xn Xt imm912 size signed wback postindex 
  | ARM_INDEXED ARM_STRH_IMM Xn Xt imm912 size signed wback postindex => arm_strh_imm2il Xn Xt imm912 size signed wback postindex (*TODO: whats size?*)
  | ARM_INDEXED ARM_LDRH_IMM Xn Xt imm912 size signed wback postindex => arm_ldrh_imm2il Xn Xt imm912 signed wback postindex
  | ARM_INDEXED ARM_LDRSH_IMM Xn Xt imm912 size signed wback postindex => arm_ldrsh_imm2il Xn Xt imm912 size signed wback postindex
  | ARM_INDEXED ARM_STR_IMM Xn Xt imm912 size signed wback postindex => arm_str_imm2il Xn Xt imm912 size signed wback postindex
  | ARM_INDEXED ARM_LDRSW_IMM Xn Xt imm912 size signed wback postindex => arm_ldrsw_imm2il Xn Xt imm912 signed wback postindex
  (*register unprivileged*)
  | ARM_REG_UNPRIVILEGED ARM_STTRB Rn Rt imm9 size => arm_sttrb2il Rn Rt imm9
  | ARM_REG_UNPRIVILEGED ARM_LDTRB Rn Rt imm9 size => arm_ldtrb2il Rn Rt imm9
  | ARM_REG_UNPRIVILEGED ARM_LDTRSB Rn Rt imm9 size => arm_ldtrsb2il Rn Rt imm9 size
  | ARM_REG_UNPRIVILEGED ARM_STTRH Rn Rt imm9 size => arm_sttrh2il Rn Rt imm9
  | ARM_REG_UNPRIVILEGED ARM_LDTRH Rn Rt imm9 size => arm_ldtrh2il Rn Rt imm9
  | ARM_REG_UNPRIVILEGED ARM_LDTRSH Rn Rt imm9 size => arm_ldtrsh2il Rn Rt imm9 size
  | ARM_REG_UNPRIVILEGED ARM_STTR Rn Rt imm9 size => arm_sttr2il Rn Rt imm9 size
  | ARM_REG_UNPRIVILEGED ARM_LDTR Rn Rt imm9 size => arm_ldtr2il Rn Rt imm9 size
  | ARM_REG_UNPRIVILEGED ARM_LDTRSW Rn Rt imm9 size => arm_ldtrsw2il Rn Rt imm9 
  (*atomic memory ops*)
  | ARM_ATOMIC ARM_LDADDB size Xn Xs Xt => arm_ldaddb2il Xn Xs Xt
  | ARM_ATOMIC ARM_LDCLRB size Xn Xs Xt => arm_ldclrb2il Xn Xs Xt
  | ARM_ATOMIC ARM_LDEORB size Xn Xs Xt => arm_ldeorb2il Xn Xs Xt
  | ARM_ATOMIC ARM_LDSETB size Xn Xs Xt => arm_ldsetb2il Xn Xs Xt
  | ARM_ATOMIC ARM_LDSMAXB size Xn Xs Xt => arm_ldsmaxb2il Xn Xs Xt
  | ARM_ATOMIC ARM_LDSMINB size Xn Xs Xt => arm_ldsminb2il Xn Xs Xt
  | ARM_ATOMIC ARM_LDUMINB size Xn Xs Xt => arm_lduminb2il Xn Xs Xt
  | ARM_ATOMIC ARM_SWPB size Xn Xs Xt => arm_swpb2il Xn Xs Xt
  | ARM_ATOMIC ARM_LDADDH size Xn Xs Xt => arm_ldaddh2il Xn Xs Xt 
  | ARM_ATOMIC ARM_LDCLRH size Xn Xs Xt => arm_ldclrh2il Xn Xs Xt
  | ARM_ATOMIC ARM_LDEORH size Xn Xs Xt => arm_ldeorh2il Xn Xs Xt
  | ARM_ATOMIC ARM_LDSETH size Xn Xs Xt => arm_ldseth2il Xn Xs Xt
  | ARM_ATOMIC ARM_LDSMAXH size Xn Xs Xt => arm_ldsmaxh2il Xn Xs Xt
  | ARM_ATOMIC ARM_LDSMINH size Xn Xs Xt => arm_ldsminh2il Xn Xs Xt
  | ARM_ATOMIC ARM_LDUMAXH size Xn Xs Xt => arm_ldumaxh2il Xn Xs Xt
  | ARM_ATOMIC ARM_LDUMINH size Xn Xs Xt => arm_lduminh2il Xn Xs Xt
  | ARM_ATOMIC ARM_SWPH size Xn Xs Xt => arm_swph2il Xn Xs Xt
  | ARM_ATOMIC ARM_LDADD size Xn Xs Xt => arm_ldadd2il size Xn Xs Xt
  | ARM_ATOMIC ARM_LDCLR size Xn Xs Xt => arm_ldclr2il size Xn Xs Xt
  | ARM_ATOMIC ARM_LDEOR size Xn Xs Xt => arm_ldeor2il size Xn Xs Xt
  | ARM_ATOMIC ARM_LDSET size Xn Xs Xt => arm_ldset2il size Xn Xs Xt
  | ARM_ATOMIC ARM_LDSMAX size Xn Xs Xt => arm_ldsmax2il size Xn Xs Xt
  | ARM_ATOMIC ARM_LDSMIN size Xn Xs Xt => arm_ldsmin2il size Xn Xs Xt
  | ARM_ATOMIC ARM_LDUMAX size Xn Xs Xt => arm_ldumax2il size Xn Xs Xt
  | ARM_ATOMIC ARM_LDUMIN size Xn Xs Xt => arm_ldumin2il size Xn Xs Xt
  | ARM_ATOMIC ARM_SWP size Xn Xs Xt => arm_swp2il size Xn Xs Xt
  (*there's a lot more here, not sure how much to add. Pages C4-240-250*)
  (*pac*)
  | ARM_LDRAA Xn Xt s imm9 wback => arm_ldraa2il Xn Xt s imm9 wback
  (*load/store register*)
  | ARM_LD_STR_REG ARM_STRB_REG Xn Xm Xt extend _ _ => arm_strb_reg2il Xn Xm Xt extend
  | ARM_LD_STR_REG ARM_LDRB_REG Xn Xm Xt extend _ _ => arm_ldrb_reg2il Xn Xm Xt extend
  | ARM_LD_STR_REG ARM_LDRSB_REG Xn Xm Xt extend size _=> arm_ldrsb_reg2il Xn Xm Xt size extend
  | ARM_LD_STR_REG ARM_STRH_REG Xn Xm Xt extend _ s => arm_strh_reg2il Xn Xm Xt extend s
  | ARM_LD_STR_REG ARM_LDRH_REG Xn Xm Xt extend _ s => arm_ldrh_reg2il Xn Xm Xt extend s
  | ARM_LD_STR_REG ARM_LDRSH_REG Xn Xm Xt extend size s => arm_ldrsh_reg2il Xn Xm Xt extend size s
  | ARM_LD_STR_REG ARM_STR_REG Xn Xm Xt extend size s => arm_str_reg2il Xn Xm Xt extend size s
  | ARM_LD_STR_REG ARM_LDR_REG Xn Xm Xt extend size s => arm_ldr_reg2il Xn Xm Xt extend size s
  | ARM_LD_STR_REG ARM_LDRSW_REG Xn Xm Xt extend _ s => arm_ldrsw_reg2il Xn Xm Xt extend s
 (* | ARM_LD_STR_REG ARM_PRFM_REG Xn Xm Xt extend _ s => havoc*)
  | UDF => Exn 4
  |_ => havoc end in
  Seq (Move R_PC (Word (a mod 2^64) 64)) il.
End Decoder.

(********** well-typedness **********)
Ltac destruct_match := repeat match goal with |- context [ match ?x with _ => _ end ] => destruct x end.
Ltac destruct_match_rmr := repeat match goal with |- context [ match ?x with _ => _ end ] => destruct x eqn:e end.
Ltac destruct_match_in H :=
  repeat match type of H with context[match ?x with _ => _ end] =>
    let e := fresh "e" in
    destruct x eqn:e
  end.

Local Definition arm8typctx_temp := (update arm8typctx (V_TEMP 0) (Some 64)).
Notation armc := arm8typctx (only parsing).
Notation armct := arm8typctx_temp (only parsing).

Ltac unfold_rec a :=
  match a with
  | ?x ?y => unfold_rec x
  | _ => unfold a
  end.

Notation temp0 := (V_TEMP 0).
Local Ltac unfold_stmt := match goal with | |- hastyp_stmt _ _ ?a _ => unfold_rec a end.
Local Ltac unfold_exp := match goal with | |- hastyp_exp _ _ ?a _ => unfold_rec a end.
Local Lemma armct_sub: armc ⊆ armct.
Proof.
  unfold pfsub. intros. unfold armct. unfold update. destruct iseq. subst. discriminate. assumption.
Qed.

Definition sizeof_c (c : typctx) (v : var) : bitwidth :=
  match c v with
  | Some s => s
  | None => 0
  end.


Local Lemma update_some:
  forall x y (c c': typctx),
    c x = Some y ->
    c ⊆ c' ->
    c ⊆ (update c' x (Some y)).
Proof.
  intros. rewrite <- store_upd_eq. assumption. apply H0. assumption.
Qed.

Local Lemma update_some_c:
  forall x (c c': typctx),
    c x = Some (sizeof_c c x) ->
    c ⊆ c' ->
    c ⊆ (update c' x (Some (sizeof_c c x))).
Proof.
  intros x c c' Hx Hsub.
  apply update_some.
  - exact Hx.
  - exact Hsub.
Qed.

Local Lemma update_fresh:
  forall (c : typctx) v w,
    c v = None ->
    c ⊆ update c v (Some w).
Proof.
  intros c v w H.
  intros x wx Hx.
  unfold update.  destruct (x==v).
  subst x. rewrite H in Hx. discriminate. assumption.
Qed.

Local Lemma update_fresh2:
  forall x y (c c': typctx),
    c x = None ->
    c ⊆ c' ->
    c ⊆ (update c' x (Some y)).
Proof.
  intros x y c c' Hnone Hsub z wz Hz.
  destruct (iseq x z).
  subst. rewrite Hnone in Hz. discriminate.
  apply Hsub in Hz. rewrite update_frame. assumption. easy.
Qed.

Local Lemma hastyp_arm_varid:
  forall c n,
    armc ⊆ c ->
    hastyp_exp c (Var (arm_varid n)) 64.
Proof.
  intros. apply hastyp_exp_weaken with (c1 := armc).
    unfold arm_varid; destruct_match; now constructor.
    assumption.
Qed.

Definition sizeof v :=
  match arm8typctx v with
  | Some s => s
  | None => 0
  end.

Local Lemma sizeof_arm_varid:
  forall n, sizeof (arm_varid n) = 64.
Proof.
  intros. unfold arm_varid. now destruct_match.
Qed.

Local Lemma typeof_arm_varid:
  forall n, arm8typctx (arm_varid n) = Some 64.
Proof.
  intros. unfold arm_varid. now destruct_match.
Qed.

Require Import Lia ZifyN ZifyBool.

Local Ltac etyp' :=
  repeat match goal with 
    | H : hastyp_exp ?c ?x ?w0 |- hastyp_exp ?c' (Cast _ _ ?x) _ =>
    eapply TCast with (w:= w0)
    | |- hastyp_exp _ (R[_,?s]) ?s => unfold arm64_R; cbn
    | |- hastyp_exp _ (SP_read ?s) ?s => unfold SP_read; cbn
    | |- hastyp_exp _ (BinOp _ (Word _ ?s) _) _ => apply TBinOp with (w := s)
    | |- hastyp_exp _ (BinOp _ _ (Word _ ?s)) _ => apply TBinOp with (w := s)
    | |- hastyp_exp ?c1 (BinOp _ (Var ?v) _) _ => apply TBinOp with (w := sizeof_c c1 v)
    | |- hastyp_exp ?c1 (BinOp _ _ (Var ?v)) _ => apply TBinOp with (w := sizeof_c c1 v)
    | |- hastyp_exp _ (Concat (Word _ ?cw1) (Word _ ?cw2)) _ => apply TConcat with (w1 := cw1) (w2 := cw2)
    | |- hastyp_exp _ (Concat _ _) _ => eapply TConcat
    | |- hastyp_exp _ (BinOp _ _ _) ?sw => apply TBinOp with (w := sw)
    | |- hastyp_exp _ (Cast _ _ (Var (V_TEMP _))) _ => eapply TCast; [apply TVar; reflexivity | try lia]; idtac "TCAST"
    | |- hastyp_exp _ (Cast _ _ (Word _ ?sw)) _ => eapply TCast with (w := sw)
    | |- hastyp_exp ?c1 (Cast _ _ (Var ?v)) _ => eapply TCast with (w := sizeof_c c1 v)
    | |- hastyp_exp _ (Cast _ _ (XtoVar _)) _ => eapply TCast with (w := 64)
    | |- hastyp_exp _ (Cast _ _ _) _ => eapply TCast
    | |- hastyp_exp _ (Extract _ _ _) ?sw => apply TExtract with (w := sw)
    | |- hastyp_exp _ (Var (arm_varid _)) 64 => apply hastyp_arm_varid
    | |- hastyp_exp _ (Var _) _ => apply TVar
    | |- hastyp_exp _ (Ite _ _ _) ?sw => apply TIte with (w := 1)
    | |- hastyp_exp _ (UnOp _ _) _ => apply TUnOp
    | |- hastyp_exp _ (Unknown _) _ => apply TUnknown
    | |- hastyp_exp _ (Word _ _) _ => apply TWord
    | |- _ <= _ => easy
    | |- _ < _ => reflexivity
    end.


Local Ltac new_etyp := repeat etyp'.

Local Ltac etyp :=
  repeat match goal with
  | H: hastyp_exp _ ?x ?s |- hastyp_exp _ (BinOp _ ?x _) _ => apply TBinOp with (w := s)
  | H: hastyp_exp _ ?x ?s |- hastyp_exp _ (BinOp _ _ ?x) _ => apply TBinOp with (w := s)
  | |- hastyp_exp _ (BinOp _ (Word _ ?s) _) _ => apply TBinOp with (w := s)
  | |- hastyp_exp _ (BinOp _ _ (Word _ ?s)) _ => apply TBinOp with (w := s)
  | |- hastyp_exp _ (BinOp ?bop _ _) _ => eapply TBinOp with (bop := bop)
  | |- hastyp_exp _ (BinOp _ (Var ?v) _) _ => apply TBinOp with (w := sizeof v)
  | |- hastyp_exp _ (BinOp _ _ (Var ?v)) _ => apply TBinOp with (w := sizeof v)

  | |- hastyp_exp _ (BinOp ?o ?x ?y) ?a =>
      match eval compute in (widthof_binop o 0 =? 0) with true => apply TBinOp with (w := a) end
         || match eval compute in (widthof_binop o 0 =? 1) with true => replace a with (widthof_binop o a); apply TBinOp with (w:=a) end

  | |- hastyp_exp _ (Concat _ _) _ => eapply TConcat

  | |- hastyp_exp _ (Cast _ _ (Word _ ?sw)) _ => eapply TCast with (w := sw)
  | |- hastyp_exp _ (Cast _ _ (Var ?v)) _ => eapply TCast with (w := sizeof v)
  | |- hastyp_exp _ (Cast _ _ ?e) _ => match e with| context[Word _ ?w] => eapply TCast with (w := w) end  
  | _ : hastyp_exp _ ?e ?w0 |- hastyp_exp _ (Cast _ _ ?e) _ =>
    eapply TCast with (w := w0); eassumption 
  | |- hastyp_exp _ (Cast _ _ _) _ => eapply TCast

  | |- match ?ct with | CAST_UNSIGNED => _ | _ => _ end => cbv; easy
  
  (*| |- _ <= _ => easy lets see if it works*)

  | |- hastyp_exp _ (Var (arm_varid _)) 64 => apply hastyp_arm_varid
  | |- hastyp_exp _ (Var _) _ => apply TVar
  | |- hastyp_exp _ (Ite _ _ _) ?a => apply TIte with (w := 1)
  | |- hastyp_exp _ (UnOp _ _) _ => apply TUnOp
  | |- hastyp_exp _ (Unknown _) _ => apply TUnknown
  | |- hastyp_exp _ (Word _ _) _ => apply TWord
  | |- hastyp_exp _ (Load _ _ _ _) _ => apply TLoad with (w := 64)
  | |- hastyp_exp _ (Store _ _ _ _ _) _ => apply TStore with (w := 64)
  | |- hastyp_exp _ (Extract ?hi ?lo ?e) ?n => replace n with (N.succ hi - lo);[eapply TExtract|]
  | X: hastyp_exp _ ?x ?a, Y: hastyp_exp _ ?y ?b |- hastyp_exp _ (Concat ?x ?y) _ => apply TConcat with (w1 := a) (w2 := b)
  | |- pfsub arm8typctx arm8typctx  => reflexivity
  | |- _ < _ => reflexivity
  | |- _ _ = Some _ => reflexivity
  end.

Local Ltac etypn size :=
  match goal with
  | |- hastyp_exp _ (BinOp _ _ _) _ => apply TBinOp with (w := size)
  | |- hastyp_exp _ (Cast _ _ _) _ => apply TCast with (w := size)
  | |- hastyp_exp _ (Extract _ _ _) _ => apply TExtract with (w := size)
  | |- _ <= _ => easy
  | |- _ < _ => reflexivity
  end.
Local Ltac etyps size := repeat (etypn size + etyp).

Print Move.
Local Ltac stypc c :=
  cbn; repeat match goal with
         | |- hastyp_stmt _ _ (Seq _ _) _ => apply TSeq with (c1 := c) (c2 := c)
         | |- hastyp_stmt _ _ (If _ _   _) _ => apply TIf with (c2 := c)
         | |- hastyp_stmt _ _ (Exn _) _ => apply TExn
         | |- hastyp_stmt _ _ (Rep _ _) _ => eapply TRep with (w:=64) (c':=c)
         | |- hastyp_stmt _ _ Nop _ => apply TNop
         | |- hastyp_stmt _ _ (Jmp _) _ => apply TJmp with (w := 64)

         | |- hastyp_stmt _ _ (Move (V_TEMP _) _) ?w' => apply TMove with (w := w')

         | |- hastyp_stmt _ _ (Move temp0 _) _ => apply TMove with (w := 64)
         | |- hastyp_stmt _ _ (Move ?v _) _ => apply TMove with (w := sizeof v); [> right | | apply update_some_c]; try reflexivity
         | |- pfsub armc armc  => reflexivity
         | |- pfsub armc armct  => apply armct_sub
         | |- hastyp_exp _ _ _  => etyp
  end.

Local Ltac stypc_w c w' c1 c2 :=
  cbn; repeat match goal with
         | |- hastyp_stmt _ _ (Seq _ _) _ => apply TSeq with (c1 := c1) (c2 := c2)
         | |- hastyp_stmt _ _ (If _ _   _) _ => apply TIf with (c2:=c2)
         | |- hastyp_stmt _ _ (Exn _) _ => apply TExn
         | |- hastyp_stmt _ _ (Rep _ _) _ => eapply TRep with (w:=w') (c:=c2)
         | |- hastyp_stmt _ _ Nop _ => apply TNop
         | |- hastyp_stmt _ _ (Jmp _) _ => apply TJmp with (w := 64)

         | |- hastyp_stmt _ ?cx (Move (V_TEMP ?v) _) _ =>
             apply TMove with (w := w') (c' := update c1 (V_TEMP v) (Some w'))

         | |- hastyp_stmt _ _ (Move temp0 _) _ => apply TMove with (w := 64)
         | |- hastyp_stmt _ _ (Move ?v _) _ => apply TMove with (w := sizeof v); [> right | | apply update_some]; try reflexivity
         | |- pfsub armc armc  => reflexivity
         | |- pfsub armc armct  => apply armct_sub
         | |- hastyp_exp _ _ _  => etyp
  end.


  Print TMove.
Local Ltac e_stypc c :=
  cbn; repeat match goal with
         | |- hastyp_stmt _ _ (Seq _ _) _ => eapply TSeq
         | |- hastyp_stmt _ _ (If _ _ _) _ => eapply TIf
         | |- hastyp_stmt _ _ (Exn _) _ => apply TExn
         | |- hastyp_stmt _ _ (Rep _ _) _ => eapply TRep
         | |- hastyp_stmt _ _ Nop _ => apply TNop
         | |- hastyp_stmt _ ?c1 (Move (V_TEMP ?v) _) _ =>
              eapply TMove with (c' := update c1 (V_TEMP v) (Some _))
         | |- hastyp_stmt _ ?c1 (Move (arm_varid _) _) _ =>
              apply TMove with (w := 64) (c' := c1); [right | | ]
         | |- hastyp_stmt _ ?c1 (Move ?v _) _ => 
              eapply TMove with (w := sizeof_c c1 v)
              (c' := update c1 (?v) (Some _)); [> right | | apply update_some_c]; try reflexivity

         | |- _ = None \/ _ = Some _ => (left; reflexivity) + (right; reflexivity)
         | |- hastyp_exp _ _ _  => new_etyp
  end.


Local Ltac styp := stypc armc.
Local Ltac styp_w w c1 c2 := stypc_w armc w c1 c2.
Local Ltac estyp := e_stypc armc .
Local Ltac estyp_c c:= e_stypc c .



(*Local Ltac hammer :=
  repeat match goal with
         | |- hastyp_stmt _ _ arm_havoc _ => apply hastyp_havoc
         | |- hastyp_stmt _ _ (arm_cond_il _ _) _ => apply hastyp_arm_cond
         | |- hastyp_exp _ R[_,_] _ => apply hastyp_R
         | |- hastyp_exp _ MemU[_, _] _ => apply hastyp_memu
         | |- hastyp_stmt _ _ (MemU[_, _] := _) _ => apply hastyp_assign_memu
         | |- hastyp_stmt _ _ (R[_] := _) _ => apply hastyp_assign_R
         | [ |- hastyp_stmt _ _ (BXWritePC _) _ ] => apply hastyp_bxwritepc
         | [ |- context [arm_data_flag] ] => unfold arm_data_flag
         | |- xbits _ ?i ?j < _ => transitivity (2^(j-i)); [> apply xbits_bound | reflexivity]
         | _ => styp
         end.*)
Local Lemma hastyp_havoc:
  forall c,
    armc ⊆ c ->
    hastyp_stmt armc c havoc c.
Proof.
  intros. unfold_stmt. stypc c; now try apply H.
Qed.
Import Lia.
Lemma hastyp_Pack_NZCV:
  forall c n z cf v,
    hastyp_exp c n 1 ->
    hastyp_exp c z 1 ->
    hastyp_exp c cf 1 ->
    hastyp_exp c v 1 ->
    hastyp_exp c (Pack_NZCV n z cf v) 4.
Proof.
  intros. unfold Pack_NZCV.
  apply TBinOp with (w := 4);
    [apply TBinOp with (w := 4) | apply TBinOp with (w := 4)].
  all: try eapply TBinOp with (w := 4); try eapply TCast with (w := 1); try eassumption; try lia; try etyps 4.
Qed.

Lemma hastyp_Unpack_NZCV:
  forall c flags,
    hastyp_exp c flags 4 ->
    let '(n, z, cf, v) := Unpack_NZCV flags in
    hastyp_exp c n 1 /\ hastyp_exp c z 1 /\ hastyp_exp c cf 1 /\ hastyp_exp c v 1.
Proof.
  intros. unfold Unpack_NZCV.
  repeat split.
  all: etyps 4; apply H.
Qed.

Lemma hastyp_arm_assign_flags:
  forall c flags,
    armc ⊆ c ->
    hastyp_exp armc flags 4 ->
    hastyp_stmt armc c (arm_assign_flags flags) armc.
Proof.
  intros. unfold arm_assign_flags. 
  destruct (Unpack_NZCV flags) as [[[n z] c0] v] eqn:Hunpack.
  pose proof (hastyp_Unpack_NZCV arm8typctx flags H0) as Hcomp.
  rewrite Hunpack in Hcomp. destruct Hcomp as [Hn [Hz [Hc0 Hc]]].
  styp; cbn; try eassumption. eapply hastyp_exp_weaken with (c1:= arm8typctx) (c2:=c); eassumption.
Qed.  

Lemma hastyp_AddWithCarry:
  forall c datasize x y carry_in,
    datasize = 32 \/ datasize = 64 ->
    hastyp_exp c x datasize ->
    hastyp_exp c y datasize ->
    hastyp_exp c carry_in 1 ->
    let '(result, nzcv) := AddWithCarry datasize x y carry_in in
    hastyp_exp c result datasize /\ hastyp_exp c nzcv 4.
Proof.
  intros c datasize x y carry_in Hd Hx Hy Hcarry.
  unfold AddWithCarry. 
  split.
  etyp; try eassumption. lia.
  apply hastyp_Pack_NZCV. 
  all: etyp; try eassumption. all: try unfold widthof_binop. all: try lia. 
  all: try rewrite N.ones_equiv; apply N.lt_pred_l; apply N.pow_nonzero; try lia.

Qed.

Local Lemma hastyp_assign_R:
  forall c n e,
    armc ⊆ c ->
    hastyp_exp armc e 64 ->
    hastyp_stmt armc c (arm_assign_R n e) armc.
Proof.
  intros. unfold arm_assign_R. styp. 
  rewrite sizeof_arm_varid. apply typeof_arm_varid.
  rewrite sizeof_arm_varid. 
  apply hastyp_exp_weaken with (c1:= arm8typctx) (c2:= c);
  assumption.
  rewrite sizeof_arm_varid. apply typeof_arm_varid. assumption.
Qed.

Local Lemma hastyp_arm_data_il:
  forall c assign assign_flags Rn result flags,
    armc ⊆ c ->
    hastyp_exp armc result 64 ->
    hastyp_exp armc flags 4 ->
    hastyp_stmt armc c (arm_data_il assign assign_flags Rn result flags) armc.
Proof.
  intros. unfold_stmt. destruct assign_flags.
  apply hastyp_arm_assign_flags; assumption.
  destruct assign. apply hastyp_assign_R; assumption.
  styp. assumption.
Qed.

Local Lemma hastyp_AddWithCarry_eq:
  forall c datasize x y carry_in r n,
    datasize = 32 \/ datasize = 64 ->
    hastyp_exp c x datasize ->
    hastyp_exp c y datasize ->
    hastyp_exp c carry_in 1 ->
    AddWithCarry datasize x y carry_in = (r, n) ->
    hastyp_exp c r datasize /\ hastyp_exp c n 4.
Proof.
  intros.
  pose proof (hastyp_AddWithCarry c datasize x y carry_in H H0 H1 H2) as Hac.
  rewrite H3 in Hac.
  assumption.
Qed.

Ltac awc_sub_branch e:=
apply hastyp_AddWithCarry_eq with (c:=arm8typctx) in e; destruct e;
try apply hastyp_arm_data_il.

Ltac awc_branch e sh:=
  destruct_match_rmr; destruct sh in e; awc_sub_branch e;
  try first[reflexivity|assumption|right;reflexivity];
  try new_etyp; try reflexivity;try lia.

Ltac awc_branch32 e sh Rn:=
  destruct_match_rmr; destruct sh in e;
  try awc_sub_branch e;
  try first[reflexivity|assumption|left;reflexivity];
  try apply TCast with (w:=32); try assumption; try lia; 
  try new_etyp; try reflexivity;try lia; 
  try destruct (Rn=?31) eqn:Hrn;
  try new_etyp; try rewrite sizeof_arm_varid; try apply typeof_arm_varid; try reflexivity; try lia.

Ltac awc sf Rn sh:=
  unfold_stmt; destruct (sf =? 1) eqn:?; destruct (Rn =? 31) eqn:?;
  destruct_match_rmr; 
  match goal with 
  | e: _ = (_,_) |- _ => awc_branch32 e sh Rn
  end.

Local Lemma hastyp_arm_data_imm:
  forall op sf s sh imm12 Rn Rd,
    imm12 < 2^12 ->
    hastyp_stmt armc armc (arm_data_imm2il op sf s sh imm12 Rn Rd) armc.
Proof.
  intros. unfold_stmt.
  destruct op eqn:?.
  - unfold_stmt. destruct (sf =? 1) eqn:?. destruct (Rn =? 31) eqn:?.
  + awc_branch e sh.
  + awc_branch e sh.
  + awc_branch32 e sh Rn. 
  - unfold_stmt. destruct (sf =? 1) eqn:?. destruct (Rn =? 31) eqn:?.
  + awc_branch e sh.
  + awc_branch e sh.
  + awc_branch32 e sh Rn. 
  - unfold_stmt. destruct (sf =? 1) eqn:?. destruct (Rn =? 31) eqn:?.
  + awc_branch e sh.
  + awc_branch e sh.
  + awc_branch32 e sh Rn. 
  - unfold_stmt. destruct (sf =? 1) eqn:?. destruct (Rn =? 31) eqn:?.
  + awc_branch e sh.
  + awc_branch e sh.
  + awc_branch32 e sh Rn.
Qed.

Local Lemma hastyp_Ones:
  forall c w e,
  w > 0 ->
  hastyp_exp c e w -> hastyp_exp c (Ones w e) w.
Proof.
  intros. assert (w < 2^w) by apply lt_pow2_lin.
  unfold Ones. new_etyp. all: first[lia|assumption].
Qed.

Local Lemma sizeof_c_lookup:
  forall c v w,
    c v = Some w ->
    sizeof_c c v = w.
Proof.
  intros c v w Hv.
  unfold sizeof_c.
  rewrite Hv.
  reflexivity.
Qed.

Local Ltac solve_armc_sub_fresh :=
  intros v k Hv;
  repeat (rewrite update_frame; [| intro Heq; subst v; discriminate Hv]);
  exact Hv.

  Local Lemma hastyp_Replicate:
  forall rettemp t w w' c x,
    armc ⊆ c ->
    w <> 0 -> w' <> 0 -> w <= w' -> t <> rettemp ->
       hastyp_exp (update (update c (V_TEMP rettemp) (Some w')) (V_TEMP t)
      (Some w)) x w ->
    hastyp_stmt armc c (Replicate rettemp t w w' x)
      (update (update c (V_TEMP rettemp) (Some w')) (V_TEMP t)
      (Some w)).
Proof.
   (*Todo- now easier that DecodeBitMasks is done.*)
   intros. unfold Replicate. assert(w' < 2 ^ w') by apply lt_pow2_lin.
   all: estyp. all: try lia. all: try reflexivity.
   all: try rewrite update_updated; unfold sizeof_c.
   rewrite update_updated. reflexivity.
   rewrite update_updated. estyp. 
   rewrite update_swap. 
   eapply hastyp_exp_weaken. eassumption. 
   eapply pfsub_update. eapply pfsub_update. 
   easy. congruence.
   rewrite update_updated. rewrite update_swap. 
   new_etyp. rewrite update_updated. 
   unfold sizeof_c. rewrite update_updated. reflexivity.
   unfold sizeof_c. rewrite update_updated. assumption.
   congruence.
   rewrite update_updated. rewrite update_swap. estyp. lia. congruence.
   rewrite update_updated. unfold widthof_binop.
   rewrite update_cancel. rewrite update_swap, update_updated. reflexivity. congruence.
   assert (w < 2^w') by lia. assert (0<w) by lia. 
   rewrite <- N.pow_0_r with (n:=2). eapply N.pow_lt_mono_r. lia. assumption. 
   rewrite update_updated. unfold widthof_binop.
   rewrite update_cancel. rewrite update_swap. rewrite update_cancel. reflexivity.
   congruence. rewrite update_swap. reflexivity. congruence. 
Qed. 



Local Ltac etypeasy :=
  match goal with
  | H: pfsub ?c ?c' |- ?c' _ = _ => apply H; try reflexivity
  | |- _ => try repeat (econstructor || assumption || lia)
  end.

Local Lemma hastyp_ConditionHolds:
  forall c n (PFSUB: pfsub arm8typctx c),  n<2^4 -> hastyp_exp c (ConditionHolds n) 1.
Proof.
  intros. unfold ConditionHolds.
  etyp; try easy; etypeasy.
Qed.

Local Lemma hastyp_XtoVar:
  forall n c (PFSUB: pfsub arm8typctx c), n < 2^5 -> hastyp_exp c (XtoVar n) 64.
Proof.
  intros. unfold XtoVar.
  etyp; try easy; etypeasy.
Qed.

Local Lemma hastyp_AllocationTagFromAddress:
  forall e n c (PFSUB:pfsub arm8typctx c), hastyp_exp c e n -> n >= 60 -> hastyp_exp c (AllocationTagFromAddress e) 4.
Proof.
  unfold AllocationTagFromAddress; intros.
  etyp; try easy; eassumption || etypeasy.
Qed.

Local Lemma hastyp_b2exp:
  forall b c, hastyp_exp c (b2exp b) 1.
Proof.
  destruct b; repeat econstructor.
Qed.

Local Lemma hastyp_AlignPow2:
  forall c e w p (T:hastyp_exp c e w) (PFSUB:pfsub arm8typctx c), 8 < 2^w -> hastyp_exp c (AlignPow2 e w p) w.
Proof.
  unfold AlignPow2. intros.
  destruct_match; try assumption; etyp; lia || assumption.
Qed.

Local Lemma hastyp_AlignCheck:
  forall c e w a (T:hastyp_exp c e w) (PFSUB:pfsub arm8typctx c), a < 2^w -> hastyp_exp c (AlignCheck e w a) 1.
Proof.
  unfold AlignCheck. intros.
  etyp; lia || assumption.
Qed.

Local Lemma hastyp_CheckSPAlignment:
  forall c (PFSUB:pfsub arm8typctx c), hastyp_stmt arm8typctx c (CheckSPAlignment) c.
Proof.
  intros; unfold CheckSPAlignment, AlignCheck.
  repeat econstructor; etypeasy. etyp. all: try lia || reflexivity.
  1,3: apply PFSUB; reflexivity. lia.
Qed.

Local Lemma hastyp_MemSingleWrite:
  forall a sz v c (T:hastyp_exp c a 64) (T2:hastyp_exp c v (sz*8)) (PFSUB:pfsub arm8typctx c),
  sz < 2^64 -> hastyp_stmt armc c (MemSingleWrite a sz v) c.
Proof.
  intros; unfold MemSingleWrite. stypc c. apply hastyp_AlignCheck.
  all: try assumption || reflexivity. 
  apply TMove with (w := sizeof V_MEM64).
    right. 3: apply update_some. 3: apply PFSUB.
    all:try reflexivity. etyp; etypeasy.
Qed.

Definition hastyp_MemWrite := hastyp_MemSingleWrite.

Local Lemma hastyp_MemRead:
  forall c a sz (T:hastyp_exp c a 64) (PFSUB:pfsub armc c), sz < 2^64 -> hastyp_exp c (MemRead a sz) (sz*8).
Proof.
  intros; unfold MemRead. etyp; etypeasy.
Qed.

Print BranchTo.
Local Lemma hastyp_BranchTo:
  forall c t (T:hastyp_exp c t 64) (PFSUB:pfsub armc c), hastyp_stmt armc c (BranchTo 64 t) c.
Proof.
  intros; unfold BranchTo, UsingAArch32.
  stypc c; etypeasy; try apply lt_pow2_lin || eassumption || reflexivity. 
Qed.

Local Lemma hastyp_HighestSetBit:
  forall w e c,
    pfsub armc c ->
    w <> 0 -> w <= 64 ->
    hastyp_exp armc e w ->
    hastyp_stmt armc armc (HighestSetBit w e)
      (update (update armc (V_TEMP 301) (Some w)) (V_TEMP 300) (Some w)).
Proof.
  intros. assert(w < 2 ^ w) by apply lt_pow2_lin.
  unfold_stmt.
  eapply TSeq.
  eapply TMove. left. reflexivity.
  eapply TBinOp. eapply TWord. assumption.
  eapply TWord. lia.
  reflexivity. 
  eapply TSeq.
  eapply TRep. unfold widthof_binop. eapply TWord. assumption.
  reflexivity.
  estyp. 
  all: try unfold widthof_binop. all: try rewrite update_cancel. all: try lia; try reflexivity.
  2: rewrite update_cancel; reflexivity. 

  eapply hastyp_exp_weaken. eassumption. apply update_fresh. reflexivity.
  eapply TMove. left. reflexivity. 
  etyp. reflexivity.  
Qed.

Local Lemma hastyp_DecodeBitMasks:
  forall immN imms immr immediate M,
    (immN < 2) -> (imms < 2^6) -> (immr < 2^6) ->
    (immediate = 0 \/ immediate = 1) ->
    (M=32 \/ M=64)->
    hastyp_stmt armc armc (DecodeBitMasks immN imms immr immediate M) 
    (update (update (update (update (update (update (update (update armc
    (V_TEMP 301) (Some 6))
    (V_TEMP 300) (Some 7))
    (V_TEMP 400) (Some 6))
    (V_TEMP 401) (Some 6))
    (V_TEMP 402) (Some 6))
    (V_TEMP 403) (Some 6))
    (V_TEMP 404) (Some 7))
    (V_TEMP 405) (Some 6)).
Proof.
  intros.
  unfold_stmt. (*split. *)
  estyp.
  eapply hastyp_HighestSetBit. reflexivity. 1-2: lia. 

  replace 7 with (1 + 6) by lia. eapply TConcat. etyp. assumption. etyp. assumption. reflexivity.
  all: try eapply hastyp_Ones.
  all: try rewrite update_frame by congruence;
  try rewrite update_updated; try reflexivity.
  all: try unfold sizeof_c ;try rewrite update_updated; try lia.
  rewrite update_swap. rewrite update_updated. lia.
  congruence.
  rewrite update_swap. rewrite update_cancel. rewrite update_swap. estyp. apply update_updated.
  1-2: try congruence.
  all: repeat estyp; repeat (rewrite update_frame; [| congruence]); try apply update_updated.
  - eapply hastyp_Replicate. solve_armc_sub_fresh. 1-4: lia. etyp.
  - eapply hastyp_stmt_weaken'. eapply hastyp_Replicate.  solve_armc_sub_fresh. 1-4: lia. etyp. solve_armc_sub_fresh.
  - eapply hastyp_Replicate. solve_armc_sub_fresh. 1-4: lia. etyp.
  - eapply hastyp_stmt_weaken'. eapply hastyp_Replicate. solve_armc_sub_fresh. 1-4: lia. etyp. solve_armc_sub_fresh.
  - eapply hastyp_Replicate. solve_armc_sub_fresh. 1-4: lia. etyp.
  - eapply hastyp_stmt_weaken'. eapply hastyp_Replicate. solve_armc_sub_fresh. 1-4: lia. etyp. solve_armc_sub_fresh.
  - eapply hastyp_Replicate. solve_armc_sub_fresh. 1-4: lia. etyp.
  - eapply hastyp_stmt_weaken'. eapply hastyp_Replicate. solve_armc_sub_fresh. 1-4: lia. etyp. solve_armc_sub_fresh.
  - eapply hastyp_Replicate. solve_armc_sub_fresh. 1-4: lia. etyp.
  - eapply hastyp_stmt_weaken'. eapply hastyp_Replicate. solve_armc_sub_fresh. 1-4: lia. etyp. solve_armc_sub_fresh.
  - eapply hastyp_Replicate. solve_armc_sub_fresh. all: try lia. etyp.
  - eapply hastyp_stmt_weaken'. eapply hastyp_Replicate. solve_armc_sub_fresh. 1-4: lia. etyp. solve_armc_sub_fresh.
  -  
  rewrite update_updated. rewrite update_frame by discriminate.
  rewrite update_updated. 
  rewrite update_swap with (x1:= temp[300])(x2:=temp[301])
  (y1:=(Some 7))(y2:=(Some 6)) by congruence. rewrite update_cancel by congruence. reflexivity.
Qed.

Local Lemma hastyp_arm_log_imm:
  forall op Rn Rd immr imms sf n_,
   (n_ < 2)->(sf < 2)->(imms < 2^6) -> (immr < 2^6)->
    hastyp_stmt armc armc (arm_log_imm2il op Rn Rd immr imms sf n_) armc.
Proof.
  intros. unfold_stmt.
  destruct op eqn:?.
  - unfold_stmt. estyp.
  6: { 
    destruct (sf=?1). all:  eapply hastyp_DecodeBitMasks.
    all: admit.
  } 
  1-3: 
  reflexivity. admit. (*XtoVar- ez, doable*)
  admit. (*ez*)
  eapply pfsub_refl. admit. (*ez from here*)


Admitted.

Local Lemma hastyp_arm_mov_imm:
  forall op Rd imm16 size shift,
    hastyp_stmt armc armc (arm_mov_imm2il op Rd imm16 size shift) armc.
Proof.
Admitted.


Theorem welltyped_arm82il:
  forall a n, hastyp_stmt armc armc (arm2il a (arm_decode n)) arm8typctx.
Proof.
  intros. unfold_stmt. styp. now apply N.mod_lt.
  remember (arm_decode n) as i. 
  destruct i. apply hastyp_arm_data_imm. admit.
Admitted. 



