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
Require Import ZArith.
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
  Notation "pats => val" := (pats, val) (at level 201, only parsing).
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
(* PC register is set to PC+8, to get the current value subtract 8. *)
Notation "'PC'" := <{{Var R_PC}+8#64}> (in custom PIL at level 65).

(* Assume we are in Execution Level 0 (User mode). NB. This simplifies some of the pseudocode. *)
(*  J1-7341
    bits(64) sp = SP[];
    stack_align_check = (SCTLR[].SA0 != '0')
    if stack_align_check && sp != Align(sp, 16) then SPAlignmentFault()
    return;
  *)

Definition XtoVar n :=
  match n with
  | 0 => Var R_X0
  | 1 => Var R_X1
  | 2 => Var R_X2
  | 3 => Var R_X3
  | 4 => Var R_X4
  | 5 => Var R_X5
  | 6 => Var R_X6
  | 7 => Var R_X7
  | 8 => Var R_X8
  | 9 => Var R_X9
  | 10 => Var R_X10
  | 11 => Var R_X11
  | 12 => Var R_X12
  | 13 => Var R_X13
  | 14 => Var R_X14
  | 15 => Var R_X15
  | 16 => Var R_X16
  | 17 => Var R_X17
  | 18 => Var R_X18
  | 19 => Var R_X19
  | 20 => Var R_X20
  | 21 => Var R_X21
  | 22 => Var R_X22
  | 23 => Var R_X23
  | 24 => Var R_X24
  | 25 => Var R_X25
  | 26 => Var R_X26
  | 27 => Var R_X27
  | 28 => Var R_X28
  | 29 => Var R_X29
  | 30 => Var R_X30
  | _ => Var R_SP
  end.

Definition arm_varid n :=
  match n with
  | 0 => R_X0 | 1 => R_X1 | 2 => R_X2 | 3 => R_X3 | 4 => R_X4 | 5 => R_X5 | 6 => R_X6 | 7 => R_X7
  | 8 => R_X8 | 9 => R_X9 | 10 => R_X10 | 11 => R_X11 | 12 => R_X12 | 13 => R_X13 | 14 => R_X14 | 15 => R_X15
  | 16 => R_X16 | 17 => R_X17 | 18 => R_X18 | 19 => R_X19 | 20 => R_X20 | 21 => R_X21 | 22 => R_X22 | 23 => R_X23
  | 24 => R_X24 | 25 => R_X25 | 26 => R_X26 | 27 => R_X27 | 28 => R_X28 | 29 => R_X29 | 30 => R_X30
  | _ => R_SP
  end.

Local Remark XtoVar_arm_varid:
  forall n, XtoVar n = Var (arm_varid n).
Proof.
  intros. destruct n as [|n]; repeat (reflexivity || destruct n as [n|n|]).
Qed.

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

Definition arm_assign_R n val := Move (arm_varid n) (Cast CAST_UNSIGNED 64 val). (*TODO: Need to fix this*)
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
  let flip := Word (xbits cond 0 1) 1 in
  let cond := xbits cond 1 4 in
  match cond with
  | 0 (* EQ_NE *) => <{flip ^ (Z=1#1)}>
  | 1 (* CS_CC *) => <{flip ^ (C=1#1)}>
  | 2 (* MI_PL *) => <{flip ^ (N=1#1)}>
  | 3 (* VS_VC *) => <{flip ^ (V=1#1)}>
  | 4 (* HI_LS *) => <{flip ^ (C=1#1 & Z=0#1)}>
  | 5 (* GE_LT *) => <{flip ^ (N=V)}>
  | 6 (* GT_LE *) => <{flip ^ (N=V & Z=0#1)}>
  | _ (* AL    *) => <{1#1}>
  end.

(* Assume LittleE only execution. The documentation for Big Endian
   is a little confusing and sparse (J1-7567). *)
Definition BigEndian : exp := <{0#1}>.

(* Configure Atomic extension, for now it seems to be supportable.
   We do not model concurrency so these are just regular operations. *)
Definition HaveAtomicExt : exp := <{1#1}>.

Definition havoc := <{ exn 0 }>.

Definition UsingAArch32 := <{ {Var R_nRW} = 1#1 }>.
Definition BranchTo w target :=
  match w with
  | 32 => <{if UsingAArch32 then jmp (ucast 64 target) else exn 0 end }>
  | 64 => <{if !UsingAArch32 then jmp target else exn 0 end}>
  | _ => <{exn 0}>
 end.

Notation "'branch' e" := (BranchTo 64 e) (in custom PIL at level 0, e at level 99).

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

(*  Returns an expression computing the highest set bit of 64-bit e.
    Returns -1#64 if e is 0 (no bits are set). *)
Definition HighestSetBit e := <{width(e)-1#64}>.

(* Return a w-bit expression of e ones *)
Definition Ones w e := <{
  (1#w << e) - 1#w
}>.

(* Replicate M-bit x until the result is N bits.  N should be a multiple of M. *)
Definition Replicate N M x :=
  (N.iter (N.pred (N/M)) (fun acc => cbits acc M x) x) mod 2^N.

Definition ROR N shift x :=
  let shift' := N.modulo shift N in
  N.lor (N.shiftr x shift') (N.shiftl x (N-shift')).

(* shift < 2^w *)
Definition RORExp w x shift :=
  let m := <{shift#w % w#w}> in <{
    ite (m = 0#w) x ((x >> m) | (x << (w#w-m)))
}>.

(* J1-7389 *)
(* Returns the wmask and tmask as a pair of M-bit Gallina Ns.
   immN - 1 bit
   imms, immr - 6 bit
   M - output bitwidth*)
Definition DecodeBitMasks (immN imms immr:N) (immediate:bool) (M:N) :=
  let len := N.pred (N.size (cbits immN 6 (N.lnot imms 6))) in
  match len, (N.shiftl 1 len) <=? M with
  | 0, _ | _, false => (0,0)
  | _, true =>
      let levels := N.ones len (* 6-bit *) in
      if immediate && ((N.land imms levels) =? levels) then (0,0) else
      let S := N.land imms levels in
      let R := N.land immr levels in
      let diff := sbop2 Z.sub 6 S R in
      let esize := N.shiftl 1 len in
      let d := xbits 0 len diff in
      let welem := N.ones (S+1) in
      let telem := N.ones (d+1) in
      let welem' := ROR esize R welem in
      let wmask := Replicate M esize welem' in
      let tmask := Replicate M esize telem in
      (wmask, tmask)
  end.
Definition wmask immN imms immr immediate M := fst (DecodeBitMasks immN imms immr immediate M).
Definition tmask immN imms immr immediate M := snd (DecodeBitMasks immN imms immr immediate M).

Section Decoder.
  Variable n : N.

(** DP Immediate*)
  Definition pc_rel :=
    let op := n.[31,32] in
    match[bits] op with
    | "0" => ARM_ADR_IMM (* ADR *)
    | "1" => ARM_ADRP_IMM (* ADRP *)
    else UDF end.

  Definition add_sub_imm :=
    let sf := n.[31,32] in
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

  (* Some details in ARMv8 Manual Section G, starting with G1-5484, and at
     https://support.arm.com/documentation/ddi0406/b/System-Level-Architecture/The-System-Level-Programmers--Model/Exceptions/Undefined-Instruction-exception *)
  (* We do not model the CPSR nor SPSR.  So just set R[14] to the next instruction and
     raise exception 0b11011. *)
  Definition UNDEF := <{var[14]:=PC-4#64}>.
  (* n = 0 \/ n = 1 *)
  Definition arm_ands_imm2il (Xn Xd immr imms sf n:N) :=
    if (sf =? 0) && (n =? 1) then None else
    let datasize := (if sf =? 1 then 64 else 32) in
    let imm := wmask n imms immr true datasize in
    let operand1 := <{lcast datasize X[Xn]}> in
    let result := <{ucast 64 (operand1 & imm#datasize)}> in
    Some <{
      var[Xd] := result;
      R_NG := result[{datasize-1}];
      R_ZR := result = 0#64;
      R_CY := 0#1;
      R_OV := 0#1
    }>.

  (* n = 0 \/ n = 1 *)
  Definition arm_and_imm2il (Xn Xd immr imms sf n:N) :=
    if (sf =? 0) && (n =? 1) then None else
    let datasize := (if sf =? 1 then 64 else 32) in
    let imm := wmask n imms immr true datasize in
    let operand1 := <{lcast datasize X[Xn]}> in
    Some <{
       var[Xd] := ucast 64 (operand1 & imm#datasize)
    }>.

  Definition arm_eor_imm2il (Xn Xd immr imms sf n:N) :=
    if (sf =? 0) && (n =? 1) then None else
    let datasize := (if sf =? 1 then 64 else 32) in
    let imm := wmask n imms immr true datasize in
    let operand1 := <{lcast datasize X[Xn]}> in
    let UNDEF := <{ (sf#1 = 0#1 & n#1 <> 0#1) }> in
    Some <{
      var[Xd] := ucast 64 (operand1 ^ imm#datasize)
    }>.

  Definition arm_orr_imm2il (Xn Xd immr imms sf n:N) :=
    if (sf =? 0) && (n =? 1) then None else
    let datasize := (if sf =? 1 then 64 else 32) in
    let imm := wmask n imms immr true datasize in
    let operand1 := <{lcast datasize X[Xn]}> in
    Some <{
      var[Xd] := ucast 64 (operand1 | imm#datasize)
    }>.

  (*logical imm*)
  Definition logical_imm :=
    let sf := n.[31,32] in
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
    let sf := n.[31,32] in
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
    if (sf =? 1) && negb (n =? 1) then None else
    if (sf =? 0) && ((negb (n =? 0)) || (negb ((xbits immr 5 6)=?0)) || (negb ((xbits imms 5 6) =? 0))) then None else
    let datasize := (if sf =? 1 then 64 else 32) in
    let R := Word immr datasize in
    let wmask := wmask n imms immr false datasize in
    let tmask := tmask n imms immr false datasize in
    let src := <{lcast datasize X[Xn]}> in
    let bot := <{{RORExp datasize src immr} & wmask#datasize}> in
    Some <{
      var[Xd] := ucast 64 (bot & tmask#datasize)
    }>.

  Definition arm_bfm_imm2il (Xn Xd immr imms sf n:N) :=
    if (sf =? 1) && negb (n =? 1) then None else
    if (sf =? 0) && ((negb (n =? 0)) || (negb ((xbits immr 5 6)=?0)) || (negb ((xbits imms 5 6) =? 0))) then None else
    let datasize := (if sf =? 1 then 64 else 32) in
    let wmask := wmask n imms immr false datasize in
    let tmask := tmask n imms immr false datasize in
    let dst := <{lcast datasize X[Xd]}> in
    let src := <{lcast datasize X[Xn]}> in
    let bot := <{(dst & {N.lnot wmask datasize}#datasize)
                  | ({RORExp datasize src immr} & wmask#datasize)}> in
    Some <{
      var[Xd] := ucast 64 ((dst & !tmask#datasize) | (bot & tmask#datasize))
    }>.

  Definition pilxbits (w:N) (n lo hi:exp) :=
    <{ (n >> lo) % (1#w << (hi-lo)) }>.

  Definition arm_sbfm_imm2il (Xn Xd immr imms sf n:N) :=
    if (sf =? 1) && negb (n =? 1) then None else
    if (sf =? 0) && ((negb (n =? 0)) || (negb ((xbits immr 5 6)=?0)) || (negb ((xbits imms 5 6) =? 0))) then None else
    let datasize := (if sf =? 1 then 64 else 32) in
    let wmask := wmask n imms immr false datasize in
    let tmask := tmask n imms immr false datasize in
    let src := <{lcast datasize X[Xn]}> in
    let topbit := (if sf =? 0 then Word 0 1 else <{src[imms]}>) in
    let bot := <{ {RORExp datasize src immr} & wmask#datasize }> in
    let top := <{ite topbit ({N.ones datasize}#datasize) (0#datasize)}> in
    Some <{
      var[Xd] := ucast 64 ((top & !tmask#datasize) | (bot & tmask#datasize))
    }>.

  Definition bitfield :=
    let sf := n.[31,32] in
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
    let sf := n.[31,32] in
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
    let offset := scast 21 64 (N.shiftl imm19 2) in
      <{if {ConditionHolds cond}
      then jmp PC + offset#64 else nop end}>.

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
      (*N*) temp[1] := (!C & !Z);
      (*Z*) temp[2] := ( C &  Z);
      (*C*) temp[3] := ( C |  Z);
      (*V*) temp[4] := (!C &  Z);
      R_NG := Xtemp[1];
      R_ZR := Xtemp[2];
      R_CY := Xtemp[3];
      R_OV := Xtemp[4]
    }>.
  Definition arm_axflag2il :=
    <{
      (*Z*) temp[2] := (Z |  V);
      (*C*) temp[3] := (C & !V);
      R_NG := 0#1;
      R_ZR := Xtemp[2];
      R_CY := Xtemp[3];
      R_OV := 0#1
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
  Definition arm_blr2il Xn := <{temp[1]:=X[Xn]; var[30] := PC+4#64; (branch Xtemp[1]); nop}>.
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
    let offset := scast 28 64 (N.shiftl imm26 2) in
    <{jmp PC+offset#64}>.

  Definition arm_bl2il imm26 :=
    let offset := scast 28 64 (N.shiftl imm26 2) in
    <{{arm_varid 30} := PC + 4#64; jmp PC+offset#64}>.

  Definition uncond_b_imm :=
    let op := n.[31,32] in
    let imm26 := n.[0,26] in
    match[bits] op with
    | "0" => ARM_B  imm26 (* B *)
    | "1" => ARM_BL imm26 (* BL *)
    else UDF end.

  Definition arm_cbz2il Xn imm19 size :=
    let offset := scast 21 64 (N.shiftl imm19 2) in
    let target := <{PC + offset#64}> in <{
    if (lcast size X[Xn]) = 0#size then {BranchTo size target} else nop end
  }>.

  Definition arm_cbnz2il Xn imm19 size :=
    let offset := scast 21 64 (N.shiftl imm19 2) in
    let target := <{PC + offset#64}> in <{
    if !((lcast size X[Xn]) = 0#size) then {BranchTo size target} else nop end
  }>.

  Definition comp_and_b :=
    let sf := n.[31,32] in
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
  Definition arm_tbz2il (Xt imm14 b5 b40:N) :=
    let pos := cbits b5 5 b40 in
    let offset := scast 16 64 (N.shiftl imm14 2) in <{
      if  X[Xt][pos] = 0#1 then branch (PC + offset#64) else nop end
  }>.

  (* C6-1340 *)
  Definition arm_tbnz2il (Xt imm14 b5 b40:N) :=
    let pos := cbits b5 5 b40 in
    let offset := scast 16 64 (N.shiftl imm14 2) in <{
      if  X[Xt][pos] = 1#1 then branch (PC + offset#64) else nop end
  }>.


  Definition test_and_b :=
    let op := n.[24] in
    let b5 := n.[31,32] in
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
  Definition arm_stg2il (Xn Xt imm9:N) (writeback postindex:bool) :=
    let offset := (scast 13 64 (N.shiftl imm9 LOG2_TAG_GRANULE)) mod 2^64 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := if postindex then <{X[Xn]}> else <{X[Xn]+offset#64}> in
    let data := <{X[Xn]}> in
    let wbblock := if negb writeback then Nop else
                   let address := if postindex then <{address+offset#64}> else address in
                   <{var[Xn]:=address}> in
    <{check; wbblock}>.

  (* Store Tag and Zero Multiple C6.2.306-1307
     This instruction's semantics are undefined for EL0. *)
  Definition arm_stzgm2il (t n:N) := havoc.

  (* Load Allocation Tag C6.2.122-962 *)
  Definition arm_ldg2il (Xn Xt imm9:N) :=
    let offset := (scast 13 64 (N.shiftl imm9 LOG2_TAG_GRANULE)) mod 2^64 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := <{Align[X[Xn]+offset#64,64,16]}> in
    <{
      check;
      (* Skip tag access *)
      var[Xt]:=address
    }>.

  Definition arm_stzg2il (Xn Xt imm9:N) (writeback postindex:bool) :=
    let offset := (scast 13 64 (N.shiftl imm9 LOG2_TAG_GRANULE)) mod 2^64 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := if postindex then <{X[Xn]}> else <{X[Xn]+offset#64}> in
    let wbblock := if negb writeback then Nop else
                   let address := if postindex then <{address+offset#64}> else address in
                   <{var[Xn]:=address}> in
    <{ check; store[address,0#{8*LOG2_TAG_GRANULE},LOG2_TAG_GRANULE]; wbblock }>.

  (* Store Allocation Tags C6-1187 *)
  Definition arm_st2g2il (Xn Xt imm9:N) (writeback postindex:bool) :=
    let offset := (scast 13 64 (N.shiftl imm9 LOG2_TAG_GRANULE)) mod 2^64 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := if postindex then <{X[Xn]}> else <{X[Xn]+offset#64}> in
    let wbblock := if negb writeback then Nop else
                   let address := if postindex then <{address+offset#64}> else address in
                   <{var[Xn]:=address}> in
    <{ check; wbblock }>.

  Definition arm_stgm2il (Xn Xt:N) := havoc.

  Definition arm_stz2g2il (Xn Xt imm9:N) (writeback postindex:bool) :=
    let offset := (scast 13 64 (N.shiftl imm9 LOG2_TAG_GRANULE)) mod 2^64 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := if postindex then <{X[Xn]}> else <{X[Xn]+offset#64}> in
    let wbblock := if negb writeback then Nop else
                   let address := if postindex then <{address+offset#64}> else address in
                   <{var[Xn]:=address}> in
    <{ check; store[address,0#{2*8*LOG2_TAG_GRANULE},{2*LOG2_TAG_GRANULE}]; wbblock }>.

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
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let undefined := <{!HaveAtomicExt | Xs#5[0] = 1#1 | Xt#5[0] = 1#1}> in
    let expectedvalue := <{
      ite BigEndian (lcast size X[Xn] ++ lcast size X[{N.succ Xn}])
                    (lcast size X[{N.succ Xn}] ++ lcast size X[Xn])}> in
    let newvalue := <{
      ite BigEndian (lcast size X[Xt] ++ lcast size X[{N.succ Xt}])
                    (lcast size X[{N.succ Xt}] ++ lcast size X[Xt])
      }> in
    <{
      if undefined then havoc else
        check;
        {MemAtomicCampareAndSwap (N.shiftl size 2) 334 <{X[Xn]}> expectedvalue newvalue};
        if BigEndian then
          var[Xs] := ucast 64 (Xtemp[334][{2*size-1}:size]);
          var[{N.succ Xs}] := ucast 64 (Xtemp[334][size:0])
        else
          var[Xs] := ucast 64 (Xtemp[334][size:0]);
          var[{N.succ Xs}] := ucast 64 (Xtemp[334][{2*size-1}:size])
        end
      end
    }>.

  Definition arm_cas2il_size (size Xn Xs Xt:N) :=
    let undefined := <{!HaveAtomicExt}> in
    let comparevalue := <{lcast size X[Xs]}> in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let newvalue := <{lcast size X[Xt]}> in <{
      if undefined then havoc else
      check;
      {MemAtomicCampareAndSwap size 334 <{X[Xn]}> comparevalue newvalue};
      var[Xs] := ucast 64 Xtemp[334]
      end
    }>.

  Definition arm_casb2il := arm_cas2il_size 8.
  Definition arm_cash2il := arm_cas2il_size 16.
  Definition arm_cas2il := arm_cas2il_size.

  (* Exclusive operations are Nops when the PE does not have exclusive access
     to memory.  We model this by using an unknown value, thus necessitating
     exploring both possible branches during symbolic execution.

      We use exp to effect the unknown behavior to let the symbolic executor handle
     the case analysis instead of duplicating code paths. *)
  Definition arm_stxr2il_constr (size Xn Xs Xt:N) (rtunknown rnunknown:bool) :=
    let bytes := N.shiftr size 3 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := if Xn=?31 then (Var R_SP) else if rnunknown then <{unknown 64}> else <{X[Xn]}> in
    let data := if rtunknown then <{unknown size}> else <{lcast size X[Xt]}> in
    <{check;
      if unknown 1 then
        (* Store not attempted, returns error bit. *)
        var[Xs] := 1#64
      else
        (* Store succeeded, but returned status may still indicate failure *)
        store[address,data,bytes];
        var[Xs] := ucast 64 (unknown 1)
      end
    }>.

  Variable oracle : N -> bool.

  Definition arm_stxr2il_size (size Xn Xs Xt:N) :=
    let constraint1 := Xs =? Xt in
    let constraint2 := (Xs =? Xn) && (negb (Xn =? 31)) in
    if (negb constraint1) && (negb constraint2) then (arm_stxr2il_constr size Xn Xs Xt false false) else
    if constraint1 then
      match oracle 1, oracle 2 with
      | false, false => UNDEF (* Constraint_UNDEF *)
      | false, true => Nop (* Constraint_NOP *)
      | true, rtunknown =>
          if constraint2 then
            match oracle 3, oracle 4 with
            | false, false => UNDEF (* Constraint_UNDEF *)
            | false, true => Nop (* Constraint_NOP *)
            | true, rnunknown =>
              (arm_stxr2il_constr size Xn Xs Xt rtunknown rnunknown)
            end
          else (arm_stxr2il_constr size Xn Xs Xt rtunknown false)
      end
    else
      if constraint2 then
        match oracle 3, oracle 4 with
        | false, false => UNDEF (* Constraint_UNDEF *)
        | false, true => Nop (* Constraint_NOP *)
        | true, rnunknown =>
          (arm_stxr2il_constr size Xn Xs Xt false rnunknown)
        end
      else (arm_stxr2il_constr size Xn Xs Xt false false).

    Definition arm_stxrb2il := arm_stxr2il_size 8.
    Definition arm_stxrh2il := arm_stxr2il_size 16.
    Definition arm_stxr2il := arm_stxr2il_size.

    Definition arm_stlxrb2il := arm_stxr2il_size 8.
    Definition arm_stlxrh2il := arm_stxr2il_size 16.
    Definition arm_stlxr2il := arm_stxr2il_size.

    Definition arm_stllr2il_size (size Xn Xt:N) :=
      let bytes := N.shiftr size 3 in
      let check := if Xn =? 31 then CheckSPAlignment else Nop in
      <{ check;
         store[X[Xn],(lcast size X[Xt]),bytes]
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
  Definition arm_stxp2il_constr (size Xn Xs Xt Xt2:N) (rtunknown rnunknown:bool) :=
    let bytes := N.shiftr size 2 in
    let el1 := <{lcast size X[Xt]}> in
    let el2 := <{lcast size X[Xt2]}> in
    let data := if rtunknown then <{unknown {size*2}}> else <{ite BigEndian (el1++el2) (el2++el1)}> in
    let address := if Xn=?31 then (Var R_SP) else if rnunknown then <{unknown 64}> else <{X[Xn]}> in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    <{
      if unknown 1 then
        (* Store not attempted, returns error bit. *)
        var[Xs] := 1#64
      else
          (* Store succeeded, but returned status may still indicate failure *)
          store[address,data,bytes];
          var[Xs] := ucast 64 (unknown 1)
      end
    }>.

  Definition arm_stxp2il_size (size Xn Xs Xt Xt2:N) :=
    let constraint1 := (Xs =? Xt) || (Xs =? Xt2) in
    let constraint2 := (Xs =? Xn) && (negb (Xn =? 31)) in
    if (negb constraint1) && (negb constraint2) then (arm_stxp2il_constr size Xn Xs Xt Xt2 false false) else
    if constraint1 then
      match oracle 1, oracle 2 with
      | false, false => UNDEF (* Constraint_UNDEF *)
      | false, true => Nop (* Constraint_NOP *)
      | true, rtunknown =>
          if constraint2 then
            match oracle 3, oracle 4 with
            | false, false => UNDEF (* Constraint_UNDEF *)
            | false, true => Nop (* Constraint_NOP *)
            | true, rnunknown =>
              (arm_stxp2il_constr size Xn Xs Xt Xt2 rtunknown rnunknown)
            end
          else (arm_stxp2il_constr size Xn Xs Xt Xt2 rtunknown false)
      end
    else
      if constraint2 then
        match oracle 3, oracle 4 with
        | false, false => UNDEF (* Constraint_UNDEF *)
        | false, true => Nop (* Constraint_NOP *)
        | true, rnunknown =>
          (arm_stxp2il_constr size Xn Xs Xt Xt2 false rnunknown)
        end
      else (arm_stxp2il_constr size Xn Xs Xt Xt2 false false).


  Definition arm_stxp2il := arm_stxp2il_size.
  Definition arm_stlxp2il := arm_stxp2il_size.

  Definition arm_ldxr2il_size (size Xn Xt:N) :=
    let bytes := N.shiftr size 3 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    <{
      check;
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

  (* Size is 32 or 64 *)
  Definition arm_ldxp2il_constr (size Xn Xt Xt2:N) (rtunknown:bool) :=
    let elsize := size in
    let datasize := elsize * 2 in
    let bytes := N.shiftr size 2 in
    let datasize := N.shiftl size 1 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := <{X[Xn]}> in
    if rtunknown then
      <{var[Xt] := (unknown 64)}>
    else if elsize =? 32 then
      let data := <{load[address,8]}> in
      <{if BigEndian then (var[Xt]:=ucast 64 data[63:32]; var[Xt2]:=ucast 64 data[31:0])
             else (var[Xt]:=ucast 64 data[31:0]; var[Xt2]:=ucast 64 data[63:32]) end}>
    else <{var[Xt]:=load[address,8]; var[Xt2]:=load[address+8#64,8]}>.

  Definition arm_ldxp2il (size Xn Xt Xt2:N) :=
    let constraint := Xt =? Xt2 in
    if constraint then
      match oracle 1, oracle 2 with
      | false, false => UNDEF
      | false, true => Nop
      | _, _ => (arm_ldxp2il_constr size Xn Xt Xt2 true)
      end
    else
      (arm_ldxp2il_constr size Xn Xt Xt2 false).

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

  (* size - bits to store in memory *)
  Definition arm_stlur2il_size size (Xn Xt imm9:N) :=
    let offset := scast 9 64 imm9 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := <{X[Xn]+offset#64}> in
    let bytes := N.shiftr size 3 in
    <{ check; store[address,X[Xn],bytes] }>.

  Definition arm_stlurb2il := arm_stlur2il_size 8.
  Definition arm_stlurh2il := arm_stlur2il_size 16.
  Definition arm_stlur2il := arm_stlur2il_size.

  (* size - size to read from memory
     signed - whether to sign extend to w'
     w' - the length to sign extend to *)
  Definition arm_ldapur2il_size_signed size (signed:bool) w' Xn Xt imm9 :=
    let offset := scast 9 64 imm9 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := <{X[Xn]+offset#64}> in
    let bytes := N.shiftr size 3 in
    let data := if signed then <{scast w' load[address,LittleE,bytes]}>
                else <{load[address,LittleE,bytes]}> in
    let result := if size =? 64 then data else <{ucast 64 data}> in
    <{ check; var[Xt] := result }>.

  Definition arm_ldapurb2il := arm_ldapur2il_size_signed 8 false 0.
  Definition arm_ldapurh2il := arm_ldapur2il_size_signed 16 false 0.
  Definition arm_ldapurw2il := arm_ldapur2il_size_signed 32 false 0.
  Definition arm_ldapur2il size := arm_ldapur2il_size_signed size false 0.

  Definition arm_ldapursb2il := arm_ldapur2il_size_signed 8 true.
  Definition arm_ldapursh2il := arm_ldapur2il_size_signed 16 true.
  Definition arm_ldapursw2il := arm_ldapur2il_size_signed 32 true.

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

  (* size - bits to read from memory
     signed - whether to sign extend to w'
     w' - the length to sign extend to *)
  Definition arm_ldr_lit2il_size_signed size (signed:bool) w' Xt imm19 :=
    let offset := scast 21 64 (N.shiftl imm19 2) in
    let address := <{PC+offset#64}> in
    let bytes := N.shiftr size 3 in
    let data := if signed then <{scast w' (load[address,bytes])}> else <{load[address,bytes]}> in
    let result := if (size =? 64) || (w' =? 64) then data else <{ucast 64 data}>
    in <{var[Xt]:=result}>.

  Definition arm_ldrb_lit2il := arm_ldr_lit2il_size_signed 8 false 0.
  Definition arm_ldrh_lit2il := arm_ldr_lit2il_size_signed 16 false 0.
  Definition arm_ldr_lit2il size := arm_ldr_lit2il_size_signed size false 0.

  Definition arm_ldrsb_lit2il := arm_ldr_lit2il_size_signed 8 true.
  Definition arm_ldrsh_lit2il := arm_ldr_lit2il_size_signed 16 true.
  Definition arm_ldrsw_lit2il := arm_ldr_lit2il_size_signed 32 true 64.


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
    let offset := (N.shiftl (scast 7 64 imm7) scale) mod 2^64 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := <{X[Xn]+offset#64}> in
    let data1 := <{X[Xt]}> in
    let data2 := <{X[Xt2]}> in
    <{ check; store[address,data1,dbytes]; store[address+dbytes#64,data2,dbytes] }>.

  Definition arm_ldnp2il_constr Xn Xt Xt2 imm7 scale (rtunknown:bool) :=
    let size := N.shiftl 8 scale in
    let dbytes := N.shiftl 1 scale in
    let offset := (N.shiftl (scast 7 64 imm7) scale) mod 2^64 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := <{X[Xn]+offset#64}> in
    let data1 := if rtunknown then <{unknown 64}> else <{ucast 64 load[address,dbytes]}> in
    let data2 := if rtunknown then <{unknown 64}> else <{ucast 64 load[address+dbytes#64,dbytes]}> in
    <{check; var[Xt] := data1; var[Xt2] := data2}>.

  Definition arm_ldnp2il Xn Xt Xt2 imm7 scale :=
    let constraint := Xt =? Xt2 in
    if negb constraint then (arm_ldnp2il_constr Xn Xt Xt2 imm7 scale false) else
    match oracle 1, oracle 2 with
    | true, true => UNDEF (* Constraint_UNDEF *)
    | false, true => Nop (* Constraint_NOP *)
    | _, _ => (arm_ldnp2il_constr Xn Xt Xt2 imm7 scale true)
    end.

  Definition arm_stp2il_constr Xn Xt Xt2 imm7 scale wback (postindex:bool) rtunknown:=
    let size := N.shiftl 8 scale in
    let dbytes := N.shiftl 1 scale in
    let offset := (N.shiftl (scast 7 64 imm7) scale) mod 2^64 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := if postindex then <{X[Xn]}> else <{X[Xn]+offset#64}> in
    let data1 := if rtunknown && (Xt =? Xn) then <{unknown 64}> else <{X[Xt]}> in
    let data2 := if rtunknown && (Xt2 =? Xn) then <{unknown 64}> else <{X[Xt2]}> in
    let wbblock := if negb wback then Nop else <{var[Xn]:=X[Xn]+offset#64}> in
    <{check; store[address,data1,dbytes]; store[address+dbytes#64,data2,dbytes]; wbblock}>.

  Definition arm_stp2il Xn Xt Xt2 imm7 scale wback postindex :=
    let constraint := wback && ((Xt=?Xn) || (Xt2=?Xn)) && (negb (Xn=?31)) in
    if negb constraint then (arm_stp2il_constr Xn Xt Xt2 imm7 scale wback postindex false) else
    match oracle 1, oracle 2 with
    | true, true => UNDEF (* Constraint_UNDEF *)
    | false, true => Nop (* Constraint_NOP *)
    | true, false => (arm_stp2il_constr Xn Xt Xt2 imm7 scale wback postindex false)
    | false, false => (arm_stp2il_constr Xn Xt Xt2 imm7 scale wback postindex true)
    end.

  (* scale is 2 or 3 *)
  Definition arm_ldp2il_constr Xn Xt Xt2 imm7 scale (wback postindex wbunknown rtunknown:bool) :=
    let size := N.shiftl 8 scale in   (* 32 or 64 *)
    let dbytes := N.shiftl 1 scale in (* 4 or 8 *)
    let datasize := N.shiftl 8 scale in
    let offset := (N.shiftl (scast 7 64 imm7) scale) mod 2^64 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := if postindex then <{X[Xn]}> else <{X[Xn]+offset#64}> in
    let data1 := if rtunknown then <{ucast 64 (unknown datasize)}> else <{ucast 64 load[address,dbytes]}> in
    let data2 := if rtunknown then <{ucast 64 (unknown datasize)}> else <{ucast 64 load[address+dbytes#64,dbytes]}> in
    let wbblock := if negb wback then Nop else
                   let address := if wbunknown then <{unknown 64}> else if postindex then <{address+offset#64}> else address in
                   <{var[Xn]:=address}> in
    <{
      var[Xt] := data1;
      var[Xt2] := data2;
      wbblock
    }>.

  (* C6-970; semantic deviation for some constraint conditions *)
  Definition arm_ldp2il (Xn Xt Xt2 imm7 scale:N) (wback postindex:bool) :=
    let constraint1 := wback && ((Xt=?Xn) || (Xt2 =? Xn)) && (negb (Xn =? 31)) in
    let constraint2 := Xt =? Xt2 in
    if (negb constraint1) && (negb constraint2) then (arm_ldp2il_constr Xn Xt Xt2 imm7 scale wback postindex false false) else
    if constraint1 then
    match oracle 1, oracle 2 with
    | true, true => UNDEF (* Constraint_UNDEF *)
    | false, true => Nop (* Constraint_NOP *)
    | true, false => let wback := false in let wbunknown := false in
        if constraint2 then
        match oracle 3, oracle 4 with
        | true, true => UNDEF (* Constraint_UNDEF *)
        | false, true => Nop (* Constraint_NOP *)
        | _, _ => (arm_ldp2il_constr Xn Xt Xt2 imm7 scale wback postindex wbunknown true)
        end
        else (arm_ldp2il_constr Xn Xt Xt2 imm7 scale wback postindex wbunknown false)
    | false, false => let wbunknown := true in
        if constraint2 then
        match oracle 3, oracle 4 with
        | true, true => UNDEF (* Constraint_UNDEF *)
        | false, true => Nop (* Constraint_NOP *)
        | _, _ => (arm_ldp2il_constr Xn Xt Xt2 imm7 scale wback postindex wbunknown true)
        end
        else (arm_ldp2il_constr Xn Xt Xt2 imm7 scale wback postindex wbunknown false)
    end
    else
      if constraint2 then
        match oracle 3, oracle 4 with
        | true, true => UNDEF (* Constraint_UNDEF *)
        | false, true => Nop (* Constraint_NOP *)
        | _, _ => (arm_ldp2il_constr Xn Xt Xt2 imm7 scale wback postindex false true)
        end
      else (arm_ldp2il_constr Xn Xt Xt2 imm7 scale wback postindex false false).

  Definition arm_stgp2il Xn Xt Xt2 imm7 (wback postindex:bool) :=
    let offset := (N.shiftl (scast 7 64 imm7) LOG2_TAG_GRANULE) mod 2^64 in
    let address := if postindex then <{X[Xn]}> else <{X[Xn]+offset#64}> in
    let data1 := <{X[Xt]}> in
    let data2 := <{X[Xt2]}> in
    let wback_block := if negb wback then Nop else
                        if postindex then <{var[Xn]:=address+offset#64}>
                        else <{var[Xn]:=address}> in
    <{store[address,data1,8]; store[address+8#64,data2,8]; wback_block}>.

  Definition arm_ldpsw2il_constr Xn Xt Xt2 imm7 (wback postindex wbunknown rtunknown:bool) :=
    let offset := (N.shiftl (scast 7 64 imm7) 2) mod 2^64 in
    let tag_checked := wback || (negb (Xn =? 31)) in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := if postindex then <{X[Xn]}> else <{X[Xn]+offset#64}> in
    let data1 := if rtunknown then <{(unknown 32)}> else <{load[address,4]}> in
    let data2 := if rtunknown then <{(unknown 32)}> else <{load[address+4#64,4]}> in
    let wbblock := if negb wback then Nop else
                   let address := if wbunknown then <{unknown 64}> else if postindex then <{address+offset#64}> else address in
                   <{var[Xn]:=address}> in
    <{check; var[Xt]:=scast 64 data1; var[Xt2]:=scast 64 data2; wbblock}>.

  Definition arm_ldpsw2il (Xn Xt Xt2 imm7:N) (wback postindex:bool) :=
    let constraint1 := wback && ((Xt=?Xn) || (Xt2=?Xn)) && (negb (Xn=?31)) in
    let constraint2 := Xt=?Xt2 in
    if constraint1 then
    match oracle 1, oracle 2 with
    | true, true => UNDEF (* Constraint_UNDEF *)
    | false, true => Nop (* Constraint_NOP *)
    | true, false => let wback := false in let wbunknown := false in
        if constraint2 then
        match oracle 3, oracle 4 with
        | true, true => UNDEF (* Constraint_UNDEF *)
        | false, true => Nop (* Constraint_NOP *)
        | _, _ => (arm_ldpsw2il_constr Xn Xt Xt2 imm7 wback postindex wbunknown true)
        end
        else (arm_ldpsw2il_constr Xn Xt Xt2 imm7 wback postindex wbunknown false)
    | false, false => let wbunknown := true in
        if constraint2 then
        match oracle 3, oracle 4 with
        | true, true => UNDEF (* Constraint_UNDEF *)
        | false, true => Nop (* Constraint_NOP *)
        | _, _ => (arm_ldpsw2il_constr Xn Xt Xt2 imm7 wback postindex wbunknown true)
        end
        else (arm_ldpsw2il_constr Xn Xt Xt2 imm7 wback postindex wbunknown false)
    end
    else
      if constraint2 then
        match oracle 3, oracle 4 with
        | true, true => UNDEF (* Constraint_UNDEF *)
        | false, true => Nop (* Constraint_NOP *)
        | _, _ => (arm_ldpsw2il_constr Xn Xt Xt2 imm7 wback postindex false true)
        end
      else (arm_ldpsw2il_constr Xn Xt Xt2 imm7 wback postindex false false).

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

  Definition arm_stur2il_size size Xn Xt imm9 :=
    let offset := scast 9 64 imm9 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := <{X[Xn]+offset#64}> in
    let bytes := N.shiftr size 3 in
    <{check; store[address, lcast size X[Xt], bytes]}>.

  Definition arm_sturb2il := arm_stur2il_size 8.
  Definition arm_sturh2il := arm_stur2il_size 16.
  Definition arm_stur2il := arm_stur2il_size.

  Definition arm_ldur2il_size size (signed:bool) w' Xn Xt imm9 :=
    let offset := scast 9 64 imm9 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := <{X[Xn]+offset#64}> in
    let bytes := N.shiftr size 3 in
    let data := if signed then <{scast w' load[address,bytes]}> else <{load[address,bytes]}> in
    let result := if (size=?64) || (w'=?64) then data else <{ucast 64 data}> in
    <{check; var[Xt] := result}>.

  Definition arm_ldurb2il := arm_ldur2il_size 8 false 0.
  Definition arm_ldurh2il := arm_ldur2il_size 16 false 0.
  Definition arm_ldur2il size := arm_ldur2il_size size false 0.

  Definition arm_ldursb2il := arm_ldur2il_size 8 true.
  Definition arm_ldursh2il := arm_ldur2il_size 16 true.
  Definition arm_ldursw2il := arm_ldur2il_size 32 true 64.

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


  (* Size is 8, 16, 32, or 64 *)
  Definition arm_str_imm2il_size_constr (size Xn Xt imm912:N) (signed wback postindex rtunknown:bool) :=
    let offset := if signed then scast 9 64 imm912 else imm912 in
    let scale := N.log2 size - 3 in
    let datasize := size in
    let bytes := N.shiftr size 3 in
    let tag_checked := wback || (negb (Xn=?31)) in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := if postindex then <{X[Xn]}> else <{X[Xn]+offset#64}> in
    let data := if rtunknown then <{unknown datasize}> else <{lcast datasize X[Xt]}> in
    let wbblock := if negb wback then Nop else
                   let address := if postindex then <{address+offset#64}> else address in
                   <{var[Xn]:=address}> in
    <{ check; store[address,data,bytes]; wbblock }>.


  (* Size is 8, 16, 32, or 64 *)
  Definition arm_str_imm2il_size (size Xn Xt imm912:N) (signed wback postindex:bool) :=
    let constraint := wback && (Xn=?Xt) && (negb (Xn=?31)) in
    if negb constraint then (arm_str_imm2il_size_constr size Xn Xt imm912 signed wback postindex false) else
    match oracle 1, oracle 2 with
    | true, true => UNDEF (* Constraint_UNDEF *)
    | false, true => Nop (* Constraint_NOP *)
    | rtunknown, false =>  (arm_str_imm2il_size_constr size Xn Xt imm912 signed wback postindex rtunknown)
    end.

  Definition arm_str_imm2il := arm_str_imm2il_size.
  Definition arm_strb_imm2il := arm_str_imm2il_size 8.
  Definition arm_strh_imm2il := arm_str_imm2il_size 16.

  Definition arm_ldr_imm2il_size_constr (size Xn Xt imm912:N) (signed wback postindex wbunknown:bool) :=
    let offset := if signed then scast 9 64 imm912 else imm912 in
    let regsize := size in
    let datasize := size in
    let bytes := N.shiftr datasize 3 in
    let tag_checked := wback || (negb (Xn =? 31)) in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := if postindex then <{X[Xn]}> else <{X[Xn]+offset#64}> in
    let data := <{load[address,bytes]}> in
    let wbblock := if negb wback then Nop else
                   let address := if wbunknown then <{unknown 64}> else if postindex then <{address+offset#64}> else address in
                   <{var[Xn]:=address}> in
    <{ check; var[Xt]:=ucast 64 data; wbblock }>.

  (* imm912 is 9bits if signed is true, 12 bits otherwise *)
  (* size is 8, 16, 32, or 64 *)
  Definition arm_ldr_imm2il_size (size Xn Xt imm912:N) (signed wback postindex:bool) :=
    let constraint := wback && (Xn =? Xt) && (negb (Xn=?31)) in
    if negb constraint then (arm_ldr_imm2il_size_constr size Xn Xt imm912 signed wback postindex false) else
    match oracle 1, oracle 2 with
    | true, true => UNDEF (* Constraint_UNDEF *)
    | false, true => Nop (* Constraint_NOP *)
    | true, false => (arm_ldr_imm2il_size_constr size Xn Xt imm912 signed false postindex false (* Contraint_WBSUPPRESS *))
    | false, false => (arm_ldr_imm2il_size_constr size Xn Xt imm912 signed wback postindex true (* Contraint_UNKNOWN *))
    end.

  Definition arm_ldr_imm2il := arm_ldr_imm2il_size.
  Definition arm_ldrb_imm2il := arm_ldr_imm2il_size 8.
  Definition arm_ldrh_imm2il := arm_ldr_imm2il_size 16.

  (* Where w is the width to load from memory (8, 16 or 32) and w'
     is the width to extend it to (32 or 64). *)
  Definition arm_ldrs_imm2il_size_constr (w w' Xn Xt imm912:N) (signed wback postindex wbunknown:bool) :=
    let offset := if signed then scast 9 64 imm912 else N.shiftl imm912 1 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := if postindex then <{X[Xn]}> else <{X[Xn]+offset#64}> in
    let bytes := N.shiftr w 3 in
    let data := <{load[address,bytes]}> in
    let wbblock := if negb wback then Nop else
                   let address := if wbunknown then <{unknown 64}> else if postindex then <{address+offset#64}> else address in
                   <{var[Xn]:=address}> in
    <{check; var[Xt] := ucast 64 (scast w' data); wbblock}>.

  Definition arm_ldrs_imm2il_size (w w' Xn Xt imm912:N) (signed wback postindex:bool) :=
    let constraint := wback && (Xn =? Xt) && (negb (Xn =? 31)) in
    if negb constraint then (arm_ldrs_imm2il_size_constr w w' Xn Xt imm912 signed wback postindex false)
    else match oracle 1, oracle 2 with
        | true, true => UNDEF (* Constraint_UNDEF *)
        | false, true => Nop (* Constraint_NOP *)
        | true, wback => (arm_ldrs_imm2il_size_constr w w' Xn Xt imm912 signed wback postindex false)
        | false, false => (arm_ldrs_imm2il_size_constr w w' Xn Xt imm912 signed wback postindex true)
         end.

  Definition arm_ldrsb_imm2il := arm_ldrs_imm2il_size 8.
  Definition arm_ldrsh_imm2il := arm_ldrs_imm2il_size 16.
  Definition arm_ldrsw_imm2il := arm_ldrs_imm2il_size 32 64.

  (*post-indexed imm*)
  (* TODO: continue here with ldrs*, this signed operation should not have a 64-bit
     setting, but the lines below instantiate such an instruction with size 64.
     This is a bug. *)
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

  Definition arm_sttr2il_size size (Xn Xt imm9:N) :=
    let offset := scast 9 64 imm9 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := <{X[Xn]+offset#64}> in
    let bytes := N.shiftr size 3 in
    <{check; store[address,lcast size X[Xt],bytes]}>.

  Definition arm_sttrb2il := arm_sttr2il_size 8.
  Definition arm_sttrh2il := arm_sttr2il_size 16.
  Definition arm_sttr2il := arm_sttr2il_size.

  Definition arm_ldtr2il_size_signed size (signed:bool) w' Xn Xt imm9 :=
    let offset := scast 9 64 imm9 in
    let address := <{X[Xn]+offset#64}> in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let bytes := N.shiftr size 3 in
    let data := if signed then <{scast w' load[address,bytes]}> else <{load[address,bytes]}> in
    let result := if (size=?64) || (w'=?64) then data else <{ucast 64 data}> in
    <{check; var[Xt]:=result}>.

  Definition arm_ldtrb2il := arm_ldtr2il_size_signed 8 false 0.
  Definition arm_ldtrh2il := arm_ldtr2il_size_signed 16 false 0.
  Definition arm_ldtr2il size := arm_ldtr2il_size_signed size false 0.

  Definition arm_ldtrsb2il := arm_ldtr2il_size_signed 8 true.
  Definition arm_ldtrsh2il := arm_ldtr2il_size_signed 16 true.
  Definition arm_ldtrsw2il := arm_ldtr2il_size_signed 32 true 64.

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

  Variant MemAtomicOp : Set:=
  | MemAtomicOp_ADD
  | MemAtomicOp_BIC
  | MemAtomicOp_EOR
  | MemAtomicOp_ORR
  | MemAtomicOp_SMAX
  | MemAtomicOp_SMIN
  | MemAtomicOp_UMAX
  | MemAtomicOp_UMIN
  | MemAtomicOp_SWP.

  (* We do not model address translation. We assume it succeeds and is apparent.
     We also assume LittleE stores and loads, but with a little bit more complexity
     we can model run-time checking. *)
  Definition MemAtomic (op:MemAtomicOp) (w:N) (value address:exp) (rettemp:N):=
    let bytes := N.shiftr w 3 in
    let nvtemp := N.succ rettemp in
    let oldvalue := <{load[address,bytes]}> in
    let newvalue := match op with
                    | MemAtomicOp_ADD  => <{oldvalue+value}>
                    | MemAtomicOp_BIC  => <{oldvalue & !value}>
                    | MemAtomicOp_EOR  => <{oldvalue ^ value}>
                    | MemAtomicOp_ORR  => <{oldvalue | value}>
                    | MemAtomicOp_SMAX => <{ite (oldvalue s> value) oldvalue value}>
                    | MemAtomicOp_SMIN => <{ite (oldvalue s> value) value oldvalue}>
                    | MemAtomicOp_UMAX => <{ite (oldvalue  > value) oldvalue value}>
                    | MemAtomicOp_UMIN => <{ite (oldvalue  > value) value oldvalue}>
                    | MemAtomicOp_SWP  => value
                    end in
    <{temp[rettemp] := oldvalue; store[address,newvalue,bytes]}>.

  Definition arm_ldatomic2il_size (op:MemAtomicOp) (size Xn Xs Xt:N) :=
    let address := <{X[Xn]}> in
    let value := <{lcast size X[Xs]}> in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    (* Only write the old value to register if it is not SP. *)
    let wbblock := if Xt =? 32 then Nop else <{var[Xt]:=ucast 64 Xtemp[100]}> in
    <{
      check;
      {MemAtomic op size value address 100};
      wbblock
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
  Definition arm_swp2il_size (size Xn Xs Xt:N) :=
    let address := <{X[Xn]}> in
    let value := <{lcast size X[Xs]}> in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    (* Only write the old value to register if it is not SP. *)
    let wbblock := <{var[Xt]:=ucast 64 Xtemp[100]}> in
    <{
      check;
      {MemAtomic MemAtomicOp_SWP size value address 100};
      wbblock
    }>.

  Definition arm_swpb2il := arm_swp2il_size 8.
  Definition arm_swph2il := arm_swp2il_size 16.
  Definition arm_swp2il := arm_swp2il_size.

  Definition arm_ldapr2il_size (size Xn Xt:N) :=
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let bytes := N.shiftr size 3 in  <{
      check;
      var[Xt] := ucast 64 {MemRead <{X[Xn]}> bytes}
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
    | "00  0  0  0  0  000" => ARM_ATOMIC ARM_LDADDB   8 Rn Rs Rt (* LDADDB, LDADDAB, LDADDALB, LDADDLB - No memory ordering variant on page C6-632 ARMv8.1 *)
    | "00  0  0  0  0  001" => ARM_ATOMIC ARM_LDCLRB   8 Rn Rs Rt (* LDCLRB, LDCLRAB, LDCLRALB, LDCLRLB -  *)
    | "00  0  0  0  0  010" => ARM_ATOMIC ARM_LDEORB   8 Rn Rs Rt (* LDEORB, LDEORAB, LDEORALB, LDEORLB - No *)
    | "00  0  0  0  0  011" => ARM_ATOMIC ARM_LDSETB   8 Rn Rs Rt (* LDSETB, LDSETAB, LDSETALB, LDSETLB - No *)
    | "00  0  0  0  0  100" => ARM_ATOMIC ARM_LDSMAXB  8 Rn Rs Rt (* LDSMAXB, LDSMAXAB, LDSMAXALB, LDSMAXLB - ARMv8.1 *)
    | "00  0  0  0  0  101" => ARM_ATOMIC ARM_LDSMINB  8 Rn Rs Rt (* LDSMINB, LDSMINAB, LDSMINALB, LDSMINLB *)
    | "00  0  0  0  0  110" => ARM_ATOMIC ARM_LDUMAXB  8 Rn Rs Rt (* LDUMAXB, LDUMAXAB, LDUMAXALB, LDUMAXLB - ARMv8.1 *)
    | "00  0  0  0  0  111" => ARM_ATOMIC ARM_LDUMINB  8 Rn Rs Rt (* LDUMINB, LDUMINAB, LDUMINALB, LDUMINLB - ARMv8.1 *)
    | "00  0  0  0  1  000" => ARM_ATOMIC ARM_SWPB     8 Rn Rs Rt (* SWPB, SWPAB, SWPALB, SWPLB - No memory ordering variant on page C6-941 *)
    | "00  0  0  1  0  000" => ARM_ATOMIC ARM_LDADDB   8 Rn Rs Rt (* LDADDB, LDADDAB, LDADDALB, LDADDLB - Release variant on page C6-632 *)
    | "00  0  0  1  0  001" => ARM_ATOMIC ARM_LDCLRB   8 Rn Rs Rt (* LDCLRB, LDCLRAB, LDCLRALB, LDCLRLB - Release variant on page C6-647 *)
    | "00  0  0  1  0  010" => ARM_ATOMIC ARM_LDEORB   8 Rn Rs Rt (* LDEORB, LDEORAB, LDEORALB, LDEORLB - *)
    | "00  0  0  1  0  011" => ARM_ATOMIC ARM_LDSETB   8 Rn Rs Rt (* LDSETB, LDSETAB, LDSETALB, LDSETLB - *)
    | "00  0  0  1  0  100" => ARM_ATOMIC ARM_LDSMAXB  8 Rn Rs Rt (* LDSMAXB, LDSMAXAB, LDSMAXALB, *)
    | "00  0  0  1  0  101" => ARM_ATOMIC ARM_LDSMINB  8 Rn Rs Rt (* LDSMINB, LDSMINAB, LDSMINALB, LDSMINLB *)
    | "00  0  0  1  0  110" => ARM_ATOMIC ARM_LDUMAXB  8 Rn Rs Rt (* LDUMAXB, LDUMAXAB, LDUMAXALB, LDUMAXLB - Release variant on page C6-727 *)
    | "00  0  0  1  0  111" => ARM_ATOMIC ARM_LDUMINB  8 Rn Rs Rt (* LDUMINB, LDUMINAB, LDUMINALB, LDUMINLB - Release variant on page C6-733 ARMv8.1 *)
    | "00  0  0  1  1  000" => ARM_ATOMIC ARM_SWPB     8 Rn Rs Rt (* SWPB, SWPAB, SWPALB, SWPLB - Release variant on page C6-941 ARMv8.1 *)
    | "00  0  1  0  0  000" => ARM_ATOMIC ARM_LDADDB   8 Rn Rs Rt (* LDADDB, LDADDAB, LDADDALB, LDADDLB - Acquire variant on page C6-632 ARMv8.1 *)
    | "00  0  1  0  0  001" => ARM_ATOMIC ARM_LDCLRB   8 Rn Rs Rt (* LDCLRB, LDCLRAB, LDCLRALB, LDCLRLB - Acquire variant on page C6-647 ARMv8.1 *)
    | "00  0  1  0  0  010" => ARM_ATOMIC ARM_LDEORB   8 Rn Rs Rt (* LDEORB, LDEORAB, LDEORALB, LDEORLB - Acquire variant on page C6-653 ARMv8.1 *)
    | "00  0  1  0  0  011" => ARM_ATOMIC ARM_LDSETB   8 Rn Rs Rt (* LDSETB, LDSETAB, LDSETALB, LDSETLB - Acquire variant on page C6-700 ARMv8.1 *)
    | "00  0  1  0  0  100" => ARM_ATOMIC ARM_LDSMAXB  8 Rn Rs Rt (* LDSMAXB, LDSMAXAB, LDSMAXALB, LDSMAXLB - Acquire variant on page C6-706 ARMv8.1 *)
    | "00  0  1  0  0  101" => ARM_ATOMIC ARM_LDSMINB  8 Rn Rs Rt (* LDSMINB, LDSMINAB, LDSMINALB, LDSMINLB - Acquire variant on page C6-712 ARMv8.1 *)
    | "00  0  1  0  0  110" => ARM_ATOMIC ARM_LDUMAXB  8 Rn Rs Rt (* LDUMAXB, LDUMAXAB, LDUMAXALB, LDUMAXLB - Acquire variant on page C6-727 ARMv8.1 *)
    | "00  0  1  0  0  111" => ARM_ATOMIC ARM_LDUMINB  8 Rn Rs Rt (* LDUMINB, LDUMINAB, LDUMINALB, LDUMINLB - Acquire variant on page C6-733 *)
    | "00  0  1  0  1  000" => ARM_ATOMIC ARM_SWPB     8 Rn Rs Rt (* SWPB, SWPAB, SWPALB, SWPLB - Acquire varianton page C6-941 *)
    | "00  0  1  0  1  100" => ARM_ATOMIC ARM_LDAPR    8 Rn Rs Rt (* Manually added, what is this LDAPRB doing in the atomic table? Its encoding matches. *)
    | "00  0  1  1  0  000" => ARM_ATOMIC ARM_LDADDB   8 Rn Rs Rt (* LDADDB, LDADDAB, LDADDALB, LDADDLB - and release variant on page C6-632 *)
    | "00  0  1  1  0  001" => ARM_ATOMIC ARM_LDCLRB   8 Rn Rs Rt (* LDCLRB, LDCLRAB, LDCLRALB, LDCLRLB - and release variant on page C6-647 *)
    | "00  0  1  1  0  010" => ARM_ATOMIC ARM_LDEORB   8 Rn Rs Rt (* LDEORB, LDEORAB, LDEORALB, LDEORLB - and release variant on page C6-653 *)
    | "00  0  1  1  0  011" => ARM_ATOMIC ARM_LDSETB   8 Rn Rs Rt (* LDSETB, LDSETAB, LDSETALB, LDSETLB - and release variant on page C6-700 *)
    | "00  0  1  1  0  100" => ARM_ATOMIC ARM_LDSMAXB  8 Rn Rs Rt (* LDSMAXB, LDSMAXAB, LDSMAXALB,LDSMAXLB - Acquire and release variant on C6-706 *)
    | "00  0  1  1  0  101" => ARM_ATOMIC ARM_LDSMINB  8 Rn Rs Rt (* LDSMINB, LDSMINAB, LDSMINALB, LDSMINLB- Acquire and release variant on page C6-712 *)
    | "00  0  1  1  0  110" => ARM_ATOMIC ARM_LDUMAXB  8 Rn Rs Rt (* LDUMAXB, LDUMAXAB, LDUMAXALB,LDUMAXLB - Acquire and release variant on C6-727 *)
    | "00  0  1  1  0  111" => ARM_ATOMIC ARM_LDUMINB  8 Rn Rs Rt (* LDUMINB, LDUMINAB, LDUMINALB,LDUMINLB - Acquire and release variant on C6-733 *)
    | "00  0  1  1  1  000" => ARM_ATOMIC ARM_SWPB     8 Rn Rs Rt (* SWPB, SWPAB, SWPALB, SWPLB - Acquire and variant on page C6-941 *)
    | "01  0  0  0  0  000" => ARM_ATOMIC ARM_LDADDH  16 Rn Rs Rt (* LDADDH, LDADDAH, LDADDALH, LDADDLH - memory ordering variant on page C6-634 *)
    | "01  0  0  0  0  001" => ARM_ATOMIC ARM_LDCLRH  16 Rn Rs Rt (* LDCLRH, LDCLRAH, LDCLRALH, LDCLRLH - No ordering variant on page C6-649 *)
    | "01  0  0  0  0  010" => ARM_ATOMIC ARM_LDEORH  16 Rn Rs Rt (* LDEORH, LDEORAH, LDEORALH, LDEORLH - No memory ordering variant on page C6-655 *)
    | "01  0  0  0  0  011" => ARM_ATOMIC ARM_LDSETH  16 Rn Rs Rt (* LDSETH, LDSETAH, LDSETALH, LDSETLH - No *)
    | "01  0  0  0  0  100" => ARM_ATOMIC ARM_LDSMAXH 16 Rn Rs Rt (* LDSMAXH, LDSMAXAH, LDSMAXALH, LDSMAXLH - No memory ordering variant on *)
    | "01  0  0  0  0  101" => ARM_ATOMIC ARM_LDSMINH 16 Rn Rs Rt (* LDSMINH, LDSMINAH, LDSMINALH, LDSMINLH *)
    | "01  0  0  0  0  110" => ARM_ATOMIC ARM_LDUMAXH 16 Rn Rs Rt (* LDUMAXH, LDUMAXAH, LDUMAXALH, LDUMAXLH - No memory ordering variant on *)
    | "01  0  0  0  0  111" => ARM_ATOMIC ARM_LDUMINH 16 Rn Rs Rt (* LDUMINH, LDUMINAH, LDUMINALH, LDUMINLH - No memory ordering variant on *)
    | "01  0  0  0  1  000" => ARM_ATOMIC ARM_SWPH    16 Rn Rs Rt (* SWPH, SWPAH, SWPALH, SWPLH - No memory ordering variant on page C6-943 *)
    | "01  0  0  1  0  000" => ARM_ATOMIC ARM_LDADDH  16 Rn Rs Rt (* LDADDH, LDADDAH, LDADDALH, LDADDLH - *)
    | "01  0  0  1  0  001" => ARM_ATOMIC ARM_LDCLRH  16 Rn Rs Rt (* LDCLRH, LDCLRAH, LDCLRALH, LDCLRLH - *)
    | "01  0  0  1  0  010" => ARM_ATOMIC ARM_LDEORH  16 Rn Rs Rt (* LDEORH, LDEORAH, LDEORALH, LDEORLH - *)
    | "01  0  0  1  0  011" => ARM_ATOMIC ARM_LDSETH  16 Rn Rs Rt (* LDSETH, LDSETAH, LDSETALH, LDSETLH - *)
    | "01  0  0  1  0  100" => ARM_ATOMIC ARM_LDSMAXH 16 Rn Rs Rt (* LDSMAXH, LDSMAXAH, LDSMAXALH,LDSMAXLH - Release variant on page C6-708 *)
    | "01  0  0  1  0  101" => ARM_ATOMIC ARM_LDSMINH 16 Rn Rs Rt (* LDSMINH, LDSMINAH, LDSMINALH, LDSMINLH *)
    | "01  0  0  1  0  110" => ARM_ATOMIC ARM_LDUMAXH 16 Rn Rs Rt (* LDUMAXH, LDUMAXAH, LDUMAXALH, LDUMAXLH - Release variant on page C6-729 *)
    | "01  0  0  1  0  111" => ARM_ATOMIC ARM_LDUMINH 16 Rn Rs Rt (* LDUMINH, LDUMINAH, LDUMINALH, LDUMINLH - Release variant on page C6-735 *)
    | "01  0  0  1  1  000" => ARM_ATOMIC ARM_SWPH    16 Rn Rs Rt (* SWPH, SWPAH, SWPALH, SWPLH - Release variant *)
    | "01  0  1  0  0  000" => ARM_ATOMIC ARM_LDADDH  16 Rn Rs Rt (* LDADDH, LDADDAH, LDADDALH, LDADDLH - *)
    | "01  0  1  0  0  001" => ARM_ATOMIC ARM_LDCLRH  16 Rn Rs Rt (* LDCLRH, LDCLRAH, LDCLRALH, LDCLRLH - *)
    | "01  0  1  0  0  010" => ARM_ATOMIC ARM_LDEORH  16 Rn Rs Rt (* LDEORH, LDEORAH, LDEORALH, LDEORLH - *)
    | "01  0  1  0  0  011" => ARM_ATOMIC ARM_LDSETH  16 Rn Rs Rt (* LDSETH, LDSETAH, LDSETALH, LDSETLH - *)
    | "01  0  1  0  0  100" => ARM_ATOMIC ARM_LDSMAXH 16 Rn Rs Rt (* LDSMAXH, LDSMAXAH, LDSMAXALH, LDSMAXLH - Acquire variant on page C6-708 *)
    | "01  0  1  0  0  101" => ARM_ATOMIC ARM_LDSMINH 16 Rn Rs Rt (* LDSMINH, LDSMINAH, LDSMINALH, LDSMINLH *)
    | "01  0  1  0  0  110" => ARM_ATOMIC ARM_LDUMAXH 16 Rn Rs Rt (* LDUMAXH, LDUMAXAH, LDUMAXALH, LDUMAXLH - Acquire variant on page C6-729 *)
    | "01  0  1  0  0  111" => ARM_ATOMIC ARM_LDUMINH 16 Rn Rs Rt (* LDUMINH, LDUMINAH, LDUMINALH, LDUMINLH - Acquire variant on page C6-735 *)
    | "01  0  1  0  1  000" => ARM_ATOMIC ARM_SWPH    16 Rn Rs Rt (* SWPH, SWPAH, SWPALH, SWPLH - Acquire variant *)
    | "01  0  1  0  1  100" => ARM_ATOMIC ARM_LDAPRH  16 Rn Rs Rt (* LDAPR... *)
    | "01  0  1  1  0  000" => ARM_ATOMIC ARM_LDADDH  16 Rn Rs Rt (* LDADDH, LDADDAH, LDADDALH, LDADDLH - *)
    | "01  0  1  1  0  001" => ARM_ATOMIC ARM_LDCLRH  16 Rn Rs Rt (* LDCLRH, LDCLRAH, LDCLRALH, LDCLRLH - *)
    | "01  0  1  1  0  010" => ARM_ATOMIC ARM_LDEORH  16 Rn Rs Rt (* LDEORH, LDEORAH, LDEORALH, LDEORLH - *)
    | "01  0  1  1  0  011" => ARM_ATOMIC ARM_LDSETH  16 Rn Rs Rt (* LDSETH, LDSETAH, LDSETALH, LDSETLH - *)
    | "01  0  1  1  0  100" => ARM_ATOMIC ARM_LDSMAXH 16 Rn Rs Rt (* LDSMAXH, LDSMAXAH, LDSMAXALH,LDSMAXLH  *)
    | "01  0  1  1  0  101" => ARM_ATOMIC ARM_LDSMINH 16 Rn Rs Rt (* LDSMINH, LDSMINAH, LDSMINALH, LDSMINLH- Acquire and release variant on page C6-714 *)
    | "01  0  1  1  0  110" => ARM_ATOMIC ARM_LDUMAXH 16 Rn Rs Rt (* LDUMAXH, LDUMAXAH, LDUMAXALH, LDUMAXLH - Acquire and release variant on *)
    | "01  0  1  1  0  111" => ARM_ATOMIC ARM_LDUMINH 16 Rn Rs Rt (* LDUMINH, LDUMINAH, LDUMINALH, LDUMINLH - Acquire and release variant on *)
    | "01  0  1  1  1  000" => ARM_ATOMIC ARM_SWPH    16 Rn Rs Rt (* SWPH, SWPAH, SWPALH, SWPLH - Acquire and *)
    | "10  0  0  0  0  000" => ARM_ATOMIC ARM_LDADD   32 Rn Rs Rt (* LDADD, LDADDA, LDADDAL, LDADDL - 32-bit, *)
    | "10  0  0  0  0  001" => ARM_ATOMIC ARM_LDCLR   32 Rn Rs Rt (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 32-bit, no *)
    | "10  0  0  0  0  010" => ARM_ATOMIC ARM_LDEOR   32 Rn Rs Rt (* LDEOR, LDEORA, LDEORAL, LDEORL - 32-bit, no *)
    | "10  0  0  0  0  011" => ARM_ATOMIC ARM_LDSET   32 Rn Rs Rt (* LDSET, LDSETA, LDSETAL, LDSETL - 32-bit, no *)
    | "10  0  0  0  0  100" => ARM_ATOMIC ARM_LDSMAX  32 Rn Rs Rt (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL - 32-bit, no memory ordering variant on page C6-710 *)
    | "10  0  0  0  0  101" => ARM_ATOMIC ARM_LDSMIN  32 Rn Rs Rt (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL - 32-bit, no memory ordering variant on page C6-716 *)
    | "10  0  0  0  0  110" => ARM_ATOMIC ARM_LDUMAX  32 Rn Rs Rt (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL - 32-bit, no memory ordering variant on page C6-731 *)
    | "10  0  0  0  0  111" => ARM_ATOMIC ARM_LDUMIN  32 Rn Rs Rt (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL  *)
    | "10  0  0  0  1  000" => ARM_ATOMIC ARM_SWP     32 Rn Rs Rt (* SWP, SWPA, SWPAL, SWPL - 32-bit, no memory ordering variant on page C6-945 ARMv8.1 *)
    | "10  0  0  1  0  000" => ARM_ATOMIC ARM_LDADD   32 Rn Rs Rt (* LDADD, LDADDA, LDADDAL, LDADDL - 32-bit, release variant on page C6-636 ARMv8.1 *)
    | "10  0  0  1  0  001" => ARM_ATOMIC ARM_LDCLR   32 Rn Rs Rt (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 32-bit, release variant on page C6-651 ARMv8.1 *)
    | "10  0  0  1  0  010" => ARM_ATOMIC ARM_LDEOR   32 Rn Rs Rt (* LDEOR, LDEORA, LDEORAL, LDEORL - 32-bit, release variant on page C6-657 ARMv8.1 *)
    | "10  0  0  1  0  011" => ARM_ATOMIC ARM_LDSET   32 Rn Rs Rt (* LDSET, LDSETA, LDSETAL, LDSETL - 32-bit, release variant on page C6-704 ARMv8.1 *)
    | "10  0  0  1  0  100" => ARM_ATOMIC ARM_LDSMAX  32 Rn Rs Rt (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL - 32-bit, release variant on page C6-710 ARMv8.1 *)
    | "10  0  0  1  0  101" => ARM_ATOMIC ARM_LDSMIN  32 Rn Rs Rt (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL - 32-bit, release variant on page C6-716 ARMv8.1 *)
    | "10  0  0  1  0  110" => ARM_ATOMIC ARM_LDUMAX  32 Rn Rs Rt (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL - 32-bit, release variant on page C6-731 ARMv8.1 *)
    | "10  0  0  1  0  111" => ARM_ATOMIC ARM_LDUMIN  32 Rn Rs Rt (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL - 32-bit, release variant on page C6-737 ARMv8.1 *)
    | "10  0  0  1  1  000" => ARM_ATOMIC ARM_SWP     32 Rn Rs Rt (* SWP, SWPA, SWPAL, SWPL - 32-bit, release variant on page C6-945 ARMv8.1 *)
    | "10  0  1  0  0  000" => ARM_ATOMIC ARM_LDADD   32 Rn Rs Rt (* LDADD, LDADDA, LDADDAL, LDADDL - 32-bit, *)
    | "0   0  1  0  0  001" => ARM_ATOMIC ARM_LDCLR   32 Rn Rs Rt (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 32-bit, acquire variant on page C6-651 ARMv8.1 *)
    | "10  0  1  0  0  010" => ARM_ATOMIC ARM_LDEOR   32 Rn Rs Rt (* LDEOR, LDEORA, LDEORAL, LDEORL - 32-bit, acquire variant on page C6-657 ARMv8.1 *)
    | "10  0  1  0  0  011" => ARM_ATOMIC ARM_LDSET   32 Rn Rs Rt (* LDSET, LDSETA, LDSETAL, LDSETL - 32-bit, acquire variant on page C6-704 ARMv8.1 *)
    | "10  0  1  0  0  100" => ARM_ATOMIC ARM_LDSMAX  32 Rn Rs Rt (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL - 32-bit, acquire variant on page C6-710 ARMv8.1 *)
    | "10  0  1  0  0  101" => ARM_ATOMIC ARM_LDSMIN  32 Rn Rs Rt (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL - 32-bit, acquire variant on page C6-716 ARMv8.1 *)
    | "10  0  1  0  0  110" => ARM_ATOMIC ARM_LDUMAX  32 Rn Rs Rt (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL - 32-bit, acquire variant on page C6-731 ARMv8.1 *)
    | "10  0  1  0  0  111" => ARM_ATOMIC ARM_LDUMIN  32 Rn Rs Rt (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL - 32-bit, acquire variant on page C6-737 ARMv8.1 *)
    | "10  0  1  0  1  000" => ARM_ATOMIC ARM_SWP     32 Rn Rs Rt (* SWP, SWPA, SWPAL, SWPL - 32-bit, acquire variant on page C6-945 ARMv8.1 *)
    | "10  0  1  0  1  100" => ARM_ATOMIC ARM_LDAPR   32 Rn Rs Rt (* LDAPR... *)
    | "10  0  1  1  0  000" => ARM_ATOMIC ARM_LDADD   32 Rn Rs Rt (* LDADD, LDADDA, LDADDAL, LDADDL - 32-bit, acquire and release variant on page C6-636 ARMv8.1 *)
    | "10  0  1  1  0  001" => ARM_ATOMIC ARM_LDCLR   32 Rn Rs Rt (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 32-bit, acquire and release variant on page C6-651 ARMv8.1 *)
    | "10  0  1  1  0  010" => ARM_ATOMIC ARM_LDEOR   32 Rn Rs Rt (* LDEOR, LDEORA, LDEORAL, LDEORL - 32-bit, acquire and release variant on page C6-657 ARMv8.1 *)
    | "10  0  1  1  0  011" => ARM_ATOMIC ARM_LDSET   32 Rn Rs Rt (* LDSET, LDSETA, LDSETAL, LDSETL - 32-bit, acquire and release variant on page C6-704 ARMv8.1 *)
    | "10  0  1  1  0  100" => ARM_ATOMIC ARM_LDSMAX  32 Rn Rs Rt (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL - 32-bit, acquire and release variant on page C6-710 ARMv8.1 *)
    | "10  0  1  1  0  101" => ARM_ATOMIC ARM_LDSMIN  32 Rn Rs Rt (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL - 32-bit, acquire and release variant on page C6-716 ARMv8.1 *)
    | "10  0  1  1  0  110" => ARM_ATOMIC ARM_LDUMAX  32 Rn Rs Rt (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL - 32-bit, acquire and release variant on page C6-731 ARMv8.1 *)
    | "10  0  1  1  0  111" => ARM_ATOMIC ARM_LDUMIN  32 Rn Rs Rt (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL - 32-bit, acquire and release variant on page C6-737 ARMv8.1 *)
    | "10  0  1  1  1  000" => ARM_ATOMIC ARM_SWP     32 Rn Rs Rt (* SWP, SWPA, SWPAL, SWPL - 32-bit, acquire and release variant on page C6-945 ARMv8.1 *)
    | "11  0  0  0  0  000" => ARM_ATOMIC ARM_LDADD   64 Rn Rs Rt (* LDADD, LDADDA, LDADDAL, LDADDL - 64-bit, no memory ordering variant on page C6-636 ARMv8.1 *)
    | "11  0  0  0  0  001" => ARM_ATOMIC ARM_LDCLR   64 Rn Rs Rt (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 64-bit, no memory ordering variant on page C6-651 *)
    | "11  0  0  0  0  010" => ARM_ATOMIC ARM_LDEOR   64 Rn Rs Rt (* LDEOR, LDEORA, LDEORAL, LDEORL - 64-bit, no memory ordering variant on page C6-657 ARMv8.1 *)
    | "11  0  0  0  0  011" => ARM_ATOMIC ARM_LDSET   64 Rn Rs Rt (* LDSET, LDSETA, LDSETAL, LDSETL - 64-bit, no memory ordering variant on page C6-704 ARMv8.1 *)
    | "11  0  0  0  0  100" => ARM_ATOMIC ARM_LDSMAX  64 Rn Rs Rt (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL - 64-bit, no memory ordering variant on page C6-710 ARMv8.1 *)
    | "11  0  0  0  0  101" => ARM_ATOMIC ARM_LDSMIN  64 Rn Rs Rt (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL - 64-bit, no memory ordering variant on page C6-716 ARMv8.1 *)
    | "11  0  0  0  0  110" => ARM_ATOMIC ARM_LDUMAX  64 Rn Rs Rt (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL - 64-bit, no memory ordering variant on page C6-731 ARMv8.1 *)
    | "11  0  0  0  0  111" => ARM_ATOMIC ARM_LDUMIN  64 Rn Rs Rt (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL - 64-bit, no memory ordering variant on page C6-737 ARMv8.1 *)
    | "11  0  0  0  1  000" => ARM_ATOMIC ARM_SWP     64 Rn Rs Rt (* SWP, SWPA, SWPAL, SWPL - 64-bit, no memory ordering variant on page C6-945 ARMv8.1 *)
    | "11  0  0  1  0  000" => ARM_ATOMIC ARM_LDADD   64 Rn Rs Rt (* LDADD, LDADDA, LDADDAL, LDADDL - 64-bit, release variant on page C6-637 ARMv8.1 *)
    | "11  0  0  1  0  001" => ARM_ATOMIC ARM_LDCLR   64 Rn Rs Rt (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 64-bit, release variant on page C6-652 ARMv8.1 *)
    | "11  0  0  1  0  010" => ARM_ATOMIC ARM_LDEOR   64 Rn Rs Rt (* LDEOR, LDEORA, LDEORAL, LDEORL - 64-bit,release variant on page C6-658 ARMv8.1 *)
    | "11  0  0  1  0  011" => ARM_ATOMIC ARM_LDSET   64 Rn Rs Rt (* LDSET, LDSETA, LDSETAL, LDSETL - 64-bit,release variant on page C6-705 ARMv8.1 *)
    | "11  0  0  1  0  100" => ARM_ATOMIC ARM_LDSMAX  64 Rn Rs Rt (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL -64-bit, release variant on page C6-711 ARMv8.1 *)
    | "11  0  0  1  0  101" => ARM_ATOMIC ARM_LDSMIN  64 Rn Rs Rt (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL -64-bit, release variant on page C6-717 ARMv8.1 *)
    | "11  0  0  1  0  110" => ARM_ATOMIC ARM_LDUMAX  64 Rn Rs Rt (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL -64-bit, release variant on page C6-732 ARMv8.1 *)
    | "11  0  0  1  0  111" => ARM_ATOMIC ARM_LDUMIN  64 Rn Rs Rt (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL - 64-bit, release variant on page C6-738ARMv8.1 *)
    | "11  0  0  1  1  000" => ARM_ATOMIC ARM_SWP     64 Rn Rs Rt (* SWP, SWPA, SWPAL, SWPL - 64-bit, release variant on page C6-946 ARMv8.1 *)
    | "11  0  1  0  0  000" => ARM_ATOMIC ARM_LDADD   64 Rn Rs Rt (* LDADD, LDADDA, LDADDAL, LDADDL - 64-bit, acquire variant on page C6-636 ARMv8.1 *)
    | "11  0  1  0  0  001" => ARM_ATOMIC ARM_LDCLR   64 Rn Rs Rt (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 64-bit,acquire variant on page C6-651 ARMv8.1 *)
    | "11  0  1  0  0  010" => ARM_ATOMIC ARM_LDEOR   64 Rn Rs Rt (* LDEOR, LDEORA, LDEORAL, LDEORL - 64-bit, acquire variant on page C6-657 ARMv8.1 *)
    | "11  0  1  0  0  011" => ARM_ATOMIC ARM_LDSET   64 Rn Rs Rt (* LDSET, LDSETA, LDSETAL, LDSETL - 64-bit,acquire variant on page C6-704 ARMv8.1 *)
    | "11  0  1  0  0  100" => ARM_ATOMIC ARM_LDSMAX  64 Rn Rs Rt (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL -64-bit, acquire variant on page C6-710 ARMv8.1 *)
    | "11  0  1  0  0  101" => ARM_ATOMIC ARM_LDSMIN  64 Rn Rs Rt (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL -64-bit, acquire variant on page C6-716 ARMv8.1 *)
    | "11  0  1  0  0  110" => ARM_ATOMIC ARM_LDUMAX  64 Rn Rs Rt (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL -64-bit, acquire variant on page C6-731 ARMv8.1 *)
    | "11  0  1  0  0  111" => ARM_ATOMIC ARM_LDUMIN  64 Rn Rs Rt (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL - 64-bit, acquire variant on page C6-737 ARMv8.1 *)
    | "11  0  1  0  1  000" => ARM_ATOMIC ARM_SWP     64 Rn Rs Rt (* SWP, SWPA, SWPAL, SWPL - 64-bit, acquire varia *)
    | "11  0  1  0  1  100" => ARM_ATOMIC ARM_LDAPR   64 Rn Rs Rt (* LDAPR... *)
    | "1   0  1  1  0  000" => ARM_ATOMIC ARM_LDADD   64 Rn Rs Rt (* LDADD, LDADDA, LDADDAL, LDADDL - 64-bit,acquire and release variant on page C6-636 ARMv8.1 *)
    | "11  0  1  1  0  001" => ARM_ATOMIC ARM_LDCLR   64 Rn Rs Rt (* LDCLR, LDCLRA, LDCLRAL, LDCLRL - 64-bit,acquire and release variant on page C6-651 ARMv8.1 *)
    | "11  0  1  1  0  010" => ARM_ATOMIC ARM_LDEOR   64 Rn Rs Rt (* LDEOR, LDEORA, LDEORAL, LDEORL - 64-bit,acquire and release variant on page C6-657 ARMv8.1 *)
    | "11  0  1  1  0  011" => ARM_ATOMIC ARM_LDSET   64 Rn Rs Rt (* LDSET, LDSETA, LDSETAL, LDSETL - 64-bit,acquire and release variant on page C6-704 ARMv8.1 *)
    | "11  0  1  1  0  100" => ARM_ATOMIC ARM_LDSMAX  64 Rn Rs Rt (* LDSMAX, LDSMAXA, LDSMAXAL, LDSMAXL -64-bit, acquire and release variant on page C6-710 ARMv8.1 *)
    | "11  0  1  1  0  101" => ARM_ATOMIC ARM_LDSMIN  64 Rn Rs Rt (* LDSMIN, LDSMINA, LDSMINAL, LDSMINL -64-bit, acquire and release variant on page C6-716 ARMv8.1 *)
    | "11  0  1  1  0  110" => ARM_ATOMIC ARM_LDUMAX  64 Rn Rs Rt (* LDUMAX, LDUMAXA, LDUMAXAL, LDUMAXL -64-bit, acquire and release variant on page C6-731 ARMv8.1 *)
    | "11  0  1  1  0  111" => ARM_ATOMIC ARM_LDUMIN  64 Rn Rs Rt (* LDUMIN, LDUMINA, LDUMINAL, LDUMINL -64-bit, acquire and release variant on page C6-737 ARMv8.1 *)
    | "11  0  1  1  1  000" => ARM_ATOMIC ARM_SWP     64 Rn Rs Rt (* SWP, SWPA, SWPAL, SWPL - 64-bit, acquire and release variant on page C6-945 *)
    else UDF end.


  (* exttype - 3bit encoding of the type of extension. See J1-7387 and 7388 *)
  (* Assign the extended value ro regt *)
  Definition ExtendReg regt (regn exttype shift:N) :=
    let len := N.min (N.shiftl 8 (N.land exttype 3)) (64-shift) in
    let exttype := <{exttype#3}> in
    let signed  := <{exttype [2]}> in
    <{if 4#3 < (shift#3) then exn 0 else nop end;
      if signed then regt := scast 64 ((lcast {len} X[regn])++0#shift)
      else           regt := ucast 64 ((lcast {len} X[regn])++0#shift)
      end
    }>.

  Definition ExtendReg' N_ reg exttype shift :=
    let val := <{lcast N_ X[reg]}> in
    let signed := N.land 4 exttype =? 4 in
    let len := N.min (N.shiftl 8 (N.land 3 exttype)) (N_-shift) in
    if signed then <{scast N_ (val[{len-1}:0]++0#shift)}>
    else <{ucast N_ (val[{len-1}:0]++0#shift)}>.

  (* size - bits to load
     signed - whether to sign extend loaded value
     w' - width to sign extend to *)
  Definition arm_ldr_reg2il_size_signed size (signed:bool) w' S Xn Xm Xt extend :=
    let shift := match size, S with
                 | 32, 1 => 2
                 | 64, 1 => 3
                 | _, _ => 0 end in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let offset := ExtendReg' 64 Xm extend shift in
    let address := <{X[Xn]+offset}> in
    let bytes := N.shiftr size 3 in
    let data := if signed then <{scast w' load[address,bytes]}> else <{load[address,bytes]}> in
    let result := if (size=?64) || (w'=?64) then data else <{ucast 64 data}> in
    <{check; var[Xt] := result}>.

  Definition arm_ldrb_reg2il := arm_ldr_reg2il_size_signed 8 false 0 0.
  Definition arm_ldrh_reg2il := arm_ldr_reg2il_size_signed 16 false 0 0.
  Definition arm_ldr_reg2il size := arm_ldr_reg2il_size_signed size false 0.

  Definition arm_ldrsb_reg2il := arm_ldr_reg2il_size_signed 8 true.
  Definition arm_ldrsh_reg2il := arm_ldr_reg2il_size_signed 16 true.
  Definition arm_ldrsw_reg2il := arm_ldr_reg2il_size_signed 32 true 64.

  Definition arm_str_reg2il_size size S Xn Xm Xt extend :=
    let shift := match size, S with
                 | 32, 1 => 2
                 | 64, 1 => 3
                 | _, _ => 0 end in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let offset := ExtendReg' 64 Xm extend shift in
    let address := <{X[Xn]+offset}> in
    let bytes := N.shiftr size 3 in
    let data := <{lcast size X[Xt]}> in
    <{check; store[address,data,bytes]}>.

  Definition arm_strb_reg2il := arm_str_reg2il_size 8 0.
  Definition arm_strh_reg2il := arm_str_reg2il_size 16 0.
  Definition arm_str_reg2il := arm_str_reg2il_size.

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
    | "00  0  00  !=011" => ARM_LD_STR_REG ARM_STRB_REG Rn Rm Rt  option_  8 S(* STRB (register) - Extended register variant on page C6-877 *)
    | "00  0  00  011  " => ARM_LD_STR_REG ARM_STRB_REG Rn Rm Rt  option_  8 S(* STRB (register) - Shifted register variant on page C6-877 *)
    | "00  0  01  !=011" => ARM_LD_STR_REG ARM_LDRB_REG Rn Rm Rt  option_  8 S(* LDRB (register) - Extended register variant on page C6-679 *)
    | "00  0  01  011  " => ARM_LD_STR_REG ARM_LDRB_REG Rn Rm Rt  option_  8 S(* LDRB (register) - Shifted register variant on page C6-679 *)
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
    | "01  0  00  -    " => ARM_LD_STR_REG ARM_STRH_REG Rn Rm Rt  option_ 16 S (* STRH (register) *)
    | "01  0  01  -    " => ARM_LD_STR_REG ARM_LDRH_REG Rn Rm Rt  option_ 16 S (* LDRH (register) *) (*TODO: Check this*)
    | "01  0  10  -    " => ARM_LD_STR_REG ARM_LDRSH_REG Rn Rm Rt option_ 16 S (* LDRSH (register) - 64-bit variant on page C6-693 *)
    | "01  0  11  -    " => ARM_LD_STR_REG ARM_LDRSH_REG Rn Rm Rt option_ 16 S (* LDRSH (register) - 32-bit variant on page C6-693 *)
    | "01  1  00  -    " => UDF (* STR (register, SIMD&FP) *)
    | "01  1  01  -    " => UDF (* LDR (register, SIMD&FP) *)
    | "1x  0  11  -    " => UDF (* Unallocated. *)
    | "1x  1  1x  -    " => UDF (* Unallocated. *)
    | "10  0  00  -    " => ARM_LD_STR_REG ARM_STR_REG Rn Rm Rt   option_    32 S (* STR (register) - 32-bit variant on page C6-873 *)
    | "10  0  01  -    " => ARM_LD_STR_REG ARM_LDR_REG Rn Rm Rt   option_    32 S (* LDR (register) - 32-bit variant on page C6-675 *)
    | "10  0  10  -    " => ARM_LD_STR_REG ARM_LDRSW_REG Rn Rm Rt option_ size S (* LDRSW (register) *)
    | "10  1  00  -    " => UDF (* STR (register, SIMD&FP) *)
    | "10  1  01  -    " => UDF (* LDR (register, SIMD&FP) *)
    | "11  0  00  -    " => ARM_LD_STR_REG ARM_STR_REG Rn Rm Rt option_ 64 S (* STR (register) - 64-bit variant on page C6-873 *)
    | "11  0  01  -    " => ARM_LD_STR_REG ARM_LDR_REG Rn Rm Rt option_ 64 S (* LDR (register) - 64-bit variant on page C6-675 *)
    | "11  0  10  -    " => ARM_LD_STR_REG ARM_PRFM_REG Rn Rm Rt option_ size S (* PRFM (register) *)
    | "11  1  00  -    " => UDF (* STR (register, SIMD&FP) *)
    | "11  1  01  -    " => UDF (* LDR (register, SIMD&FP) *)
    else UDF end.


  (* Assume AuthDA and AuthDB are nops. *)
  Definition arm_ldraa2il_constr (Xn Xt S imm9:N) (wback wbunknown:bool) :=
    let offset := (N.shiftl (scast 10 64 (cbits S 9 imm9)) 3) mod 2^64 in
    let check := if Xn =? 31 then CheckSPAlignment else Nop in
    let address := <{X[Xn]+offset#64}> in
    let data := <{load[address, 8]}> in
    let wbblock := if negb wback then Nop else
                   let address := if wbunknown then <{unknown 64}> else address in
                   <{var[Xn] := address}> in
    <{check; var[Xt] := data; wbblock}>.

  Definition arm_ldraa2il (Xn Xt S imm9:N) (wback:bool) :=
    let constraint := wback && (Xn=?Xt) && (negb (Xn=?31)) in
    if negb constraint then (arm_ldraa2il_constr Xn Xt S imm9 wback false) else
    match oracle 1, oracle 2 with
        | true, true => UNDEF (* Constraint_UNDEF *)
        | false, true => Nop (* Constraint_NOP *)
        | true, wback => (arm_ldraa2il_constr Xn Xt S imm9 wback false)
        | false, false => (arm_ldraa2il_constr Xn Xt S imm9 wback true)
    end.

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
    let sf := n.[31,32] in
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
    let sf := n.[31,32] in
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
    let sf := n.[31,32] in
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
    let sf := n.[31,32] in
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
    let sf := n.[31,32] in
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
    let sf := n.[31,32] in
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
    let sf := n.[31,32] in
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
    let sf := n.[31,32] in
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
    let sf := n.[31,32] in
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
    let sf := n.[31,32] in
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
    let sf := n.[31,32] in
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
    let sf := n.[31,32] in
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
  Definition ExtendReg2 reg exttype datasize (shift:N):=
  if (N.ltb 4 shift) then Unknown shift else
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
  (* so my like min*)
  let extended_slice := Cast cast datasize slice in
  BinOp OP_LSHIFT extended_slice (Word shift datasize).

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
  (**let result64 := if sf =? 1 then result else Cast CAST_UNSIGNED 64 result in*)
  arm_data_il assign assign_flags Rn result (Unknown 4)
  end.

  (*op : the actual AddWithCarry
  instr : for ANDS and BICS*)
  Definition arm_data_r_addwithcarry (cond sf s shift Rm:N) imm6 (Rn:N) (assign assign_flag:bool) (op:exp -> exp -> exp->exp*exp) :=
  let datasize := if sf =? 1 then 64 else 32 in
  let shift_type := DecodeShift shift in
  if shift=? 3 then Nop else
  match (sf, (N.testbit imm6 5)) with
  |(0, true) => Nop
  | _ =>  let operand2 := ShiftReg Rm shift_type (Word imm6 datasize) datasize in
          let operand1 := R[ Rn , datasize] in
  let (result, nzcv) := op operand1 operand2 (Unknown datasize) in
  (*assign=assign to register, assign_flag=set flag values*)
 (**let result64 := if sf =? 1 then result else Cast CAST_UNSIGNED 64 result in*)
  arm_data_il assign assign_flag Rn result nzcv
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
 (***let result64 := if sf =? 1 then result else Cast CAST_UNSIGNED 64 result in*)
  arm_data_il assign assign_flag reg_n result nzcv.

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
  (**let mod2 := Cast CAST_UNSIGNED 64 (BinOp OP_MOD operand2 (Word datasize datasize)) in*)
  let mod2 :=  BinOp OP_MOD operand2 (Word datasize datasize) in
  let result := ShiftReg Rn shift_type (mod2) datasize in
  (*let result64 := if sf =? 1 then result else Cast CAST_UNSIGNED 64 result in*)
  arm_data_il assign assign_flags Rd result (Unknown 4)
  .

  Definition arm_data_r_with_carry (sf Rm Rn Rd:N) (assign assign_flags: bool) (op: exp -> exp -> exp->exp*exp):=
  let datasize := if sf =? 1 then 64 else 32 in
  let operand2 := R[ Rm , datasize] in
  let operand1 := R[ Rn, datasize ] in
  let (result,flags) := op operand1 operand2 (Word 0 1) in
  let flags :=(Unknown 4) in
  (*let result64 := if sf =? 1 then result else Cast CAST_UNSIGNED 64 result in*)
  arm_data_il assign assign_flags Rd result flags
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
  let flags := nzcv_final in
  (*if condition holds, nzcv final is the new flags from AddWithCarry else its just the value we read in*)
  arm_data_il false true Rn result flags
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
    (*let result64 := if sf =? 1 then result else Cast CAST_UNSIGNED 64 result in*)
    arm_data_il assign assign_flag Rd result nzcv
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
    arm_data_il false true Rn result nzcv_final
    .

  Definition arm_data_imm2il op sf s sh imm12 Rn Rd:=
  let datasize := if sf =? 1 then 64 else 32 in
  match op with
  | ARM_ADD_IMM => arm_data_i_addwithcarry datasize sf s sh imm12 Rn Rd true false (fun a b _ => AddWithCarry datasize a b (Word 0 1))
  | ARM_ADDS_IMM => arm_data_i_addwithcarry datasize sf s sh imm12 Rn Rd true true (fun a b _ => AddWithCarry datasize a b (Word 0 1))
  | ARM_SUB_IMM => arm_data_i_addwithcarry datasize sf s sh imm12 Rn Rd true false (fun a b _ => AddWithCarry datasize a (UnOp OP_NOT b) (Word 1 1))
  | ARM_SUBS_IMM => arm_data_i_addwithcarry datasize sf s sh imm12 Rn Rd true true (fun a b _ => AddWithCarry datasize a (UnOp OP_NOT b) (Word 1 1))
  end.

  (*TODO: change these defns using arm_data_i_addwithcarry*)
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

  Definition arm_decode n :=
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

(********** well-typedness **********)
Ltac destruct_match := repeat match goal with |- context [ match ?x with _ => _ end ] => destruct x end.
Ltac destruct_match_rmr := repeat match goal with |- context [ match ?x with _ => _ end ] => destruct x eqn:e end.
Ltac destruct_match_in H :=
  repeat match type of H with context[match ?x with _ => _ end] =>
    let e := fresh "e" in
    destruct x eqn:e
  end.

Local Definition arm8typctx_temp sf := (update (update (update (update (update (update (update (update (update (update (update arm8typctx
    (V_TEMP 301) (Some 6))
    (V_TEMP 300) (Some 7))
    (V_TEMP 400) (Some 6))
    (V_TEMP 401) (Some 6))
    (V_TEMP 402) (Some 6))
    (V_TEMP 403) (Some 6))
    (V_TEMP 404) (Some 7))
    (V_TEMP 405) (Some 6))
    (V_TEMP 990) (Some (if sf =? 1 then 64 else 32)))
    (V_TEMP 980) (Some (if sf =? 1 then 64 else 32)))
    (V_TEMP 1000) (Some (if sf =? 1 then 64 else 32)))
    .
Notation armc := arm8typctx (only parsing).
Notation armct := arm8typctx_temp (only parsing).

Ltac unfold_rec a :=
  match a with
  | ?x ?y => unfold_rec x
  | _ => unfold a
  end.

Ltac destruct_rec a :=
  match a with
  | if ?x then ?y else ?z => destruct_rec x
  | _ => destruct a
  end.

Notation temp0 := (V_TEMP 0).
Local Ltac unfold_stmt := match goal with | |- hastyp_stmt _ _ ?a _ => unfold_rec a end.
Local Ltac unfold_exp := match goal with | |- hastyp_exp _ _ ?a _ => unfold_rec a end.
Local Lemma armct_sub sf: armc ⊆ armct sf.
Proof.
  intros x y H. unfold arm8typctx_temp. rewrite ?update_frame by (intro; subst; discriminate).
  assumption.
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

Definition empty (v:var) : option N := None.

Local Lemma pfsub_empty:
  forall c, pfsub empty c.
Proof.
  intros; intros x y H; discriminate.
Qed.

Local Lemma hastyp_exp_empty:
  forall c e n, hastyp_exp empty e n -> hastyp_exp c e n.
Proof.
  intros; eapply hastyp_exp_weaken;[eassumption | apply pfsub_empty].
Qed.



Require Import Lia ZifyN ZifyBool.
Ltac Zify.zify_pre_hook ::=
  rewrite ?N.shiftl_mul_pow2, ?N.shiftr_div_pow2;
  unfold widthof_binop; (idtac + apply f_equal).

  (* Simplifies goals reading vars from a context that is a superset of armc. Example simplified expression:

   (sizeof_c (c[temp[ 9000] := Some 64][temp[ 1000] := Some 64][temp[ 1000] := Some 64]) V_MEM64) *)
Local Ltac simpl_c :=
  unfold sizeof_c, widthof_binop; repeat rewrite update_frame by discriminate; repeat rewrite update_updated;
  repeat match goal with
  | PF: pfsub armc ?c |- context[?c ?v] =>
      match v with V_TEMP _ => fail | _ => idtac end;
      let PFspec := fresh "PF" in
      pose proof (PFspec:=PF v); cbn -[N.pow N.mul] in PFspec;
      try rewrite (N.mul_comm 8) in PFspec; (*rewrite memory bitwidth for the static semantics*)
      rewrite (PFspec _ (eq_refl _));
      clear PFspec
  end.

Local Lemma context_update_some {A B:Type} {E:EqDec A}:
  forall c v x (y:B), update c v None x = Some y -> x <> v.
Proof.
  intros; destruct (iseq x v).
    subst; rewrite update_updated in *; discriminate.
    assumption.
Qed.
(* [red_ccases] reduces the cases to consider in a context-read equality goal
    by discriminating on variables that have been updated to [None].  E.g.,
   turns
        H : (c[temp[ 1000] := None][temp[ 9000] := None]) x = Some y
   into
        H : c x = Some y
        NEQ : x <> temp[ 9000]
        NEQ0 : x <> temp[ 1000]
*)
Local Ltac red_ccases :=
  repeat match goal with
  | H: update _ _ None _ = Some _ |- _ => repeat (
      let NEQ := fresh "NEQ" in
      pose proof (NEQ:=context_update_some _ _ _ _ H);
      rewrite update_frame in H by assumption
      )
  | HNone: ?c ?v = None, HSome: ?c ?v2 = Some _ |- _ =>
      assert (v2<>v) by (intro;subst;now rewrite HNone in HSome);
      clear HNone
  | _ => idtac
  end.

Local Lemma temp_None:
forall n y,
armc (V_TEMP n) = Some y -> False.
Proof.
  intros. assert (armc (V_TEMP n0) = None) by reflexivity.
  discriminate.
Qed.

Local Lemma temp_None_L:
forall n y,
Some y = armc (V_TEMP n)-> False.
Proof.
  intros. assert (None = armc (V_TEMP n0)) by reflexivity.
  discriminate.
Qed.

Local Lemma armvarid_neq_temp:
  forall n t, arm_varid n <> V_TEMP t.
Proof.
  intros. unfold arm_varid. destruct_match; discriminate.
Qed.

Local Lemma armvarid_neq_mem:
  forall n, arm_varid n <> V_MEM64.
Proof.
  intros n0 EQ. pose proof (H:=typeof_arm_varid n0). now rewrite EQ in H.
Qed.

(* [cget] solves or simplifies [c x = Some _] goals where c has updates and
   maybe we need to appeal to a pfsub hypothesis. *)
Local Ltac cget :=
  rewrite ?update_frame by (discriminate||(idtac+symmetry);(apply armvarid_neq_temp + apply armvarid_neq_mem) ||intros H;inversion H;lia);
  ((rewrite update_updated; try reflexivity)
  || lazymatch goal with
     | H: pfsub armc ?c |- ?c _ = Some _ => apply H; simpl; try (reflexivity || apply typeof_arm_varid)
     | H: pfsub ?c' ?c |- ?c _ = Some _ => apply H; cget
     end).

(* c_varx solves more complicated context equations like the one below:

PF : arm8typctx ⊆ c
H : (c[temp[ 1000] := None][temp[ 9000] := None]) x = Some y
========================= (1 / 1)
(c[temp[ 9000] := Some 64][temp[ 1000] := Some 64][temp[ 1000] := Some 64]
 [V_MEM64 := Some (8 * 2 ^ 64)]) x = Some y *)
Ltac c_varx :=
  red_ccases;
  repeat match goal with
  (* Solvers *)
  | NE: ?x <> ?v |- update _ ?v _ ?x = _ => rewrite update_frame by assumption
  | H: ?x |- ?x => assumption
  | H: ?x = Some _, H2: ?x = None |- _ => now rewrite H in H2
  (* Used when proving that armc is a satisfactory output context. *)
  | PF: pfsub armc ?c |- ?c _ = _ => apply PF; assumption
  | PF: pfsub armc ?c |- Some _ = ?c _ => symmetry; apply PF; (reflexivity || assumption || apply typeof_arm_varid)
  | PF: pfsub armc ?c |- context[?c ?v] => rewrite (PF v _ (eq_refl _)); rewrite ?(N.mul_comm 8); reflexivity
  (* Reducers *)
  | PF:arm8typctx ⊆ _, EQ:?c' ?x = _ |- update ?c ?v  (Some ?val) ?x = Some ?y =>
        destruct (x == v);
          [ subst; rewrite update_updated;
            (* First case solves when the output context is a modification of the input;
                second case solves when the output context is weakend to arm8typctx.
                The latter case is useful for simplifying and indicating the theorems for
                terminal lifter code as opposed to internal auxiliary functions. *)
            first [ assumption
                  | specialize (PF v val eq_refl) || specialize (PF v val (typeof_arm_varid _));
                    rewrite PF, <- EQ in *; reflexivity
                  | discriminate ||
                    match goal with | EQ: armc _ = Some ?y |- _ = Some ?y =>
                      rewrite <-EQ, ?typeof_arm_varid; reflexivity
                    end
                  ]
         | rewrite ?update_frame in * by assumption ]
  | PF: pfsub armc _, EQ: ?c' ?x = _|- update ?c ?v (Some ?val) ?x = Some ?y => destruct (iseq x v);
      [subst;rewrite update_updated; (specialize (PF v val (eq_refl _)) || specialize (PF v val (typeof_arm_varid _))); rewrite PF, <-EQ in *; reflexivity
      |rewrite update_frame by assumption]
  | EQ: _ _ = ?y |- update _ ?v _ ?x = ?y => destruct (x==v);
      [subst;erewrite update_updated,?update_frame in * by (discriminate||apply armvarid_neq_temp||intros H;inversion H;lia);
         rewrite <-EQ
         |rewrite update_frame by assumption]
  (* Adding this case breaks proofs. *)
  (*| |- context[update ?c ?v (Some _) ?x] => *)
  (*    rewrite (update_updated c x) ||*)
  (*    let EQ:=fresh "EQ" in*)
  (*    let NEQ:=fresh "NEQ" in*)
  (*    destruct (x==v) as [EQ|NEQ];[rewrite EQ in *; clear EQ|rewrite ?(update_frame _ _ _ _ NEQ)]*)
  end.

Local Lemma armc_update_reg:
  forall n, pfsub armc (update armc (arm_varid n) (Some 64)).
Proof.
  intros. rewrite <-store_upd_eq.
    reflexivity.
    apply typeof_arm_varid.
Qed.



(* Prove pfsub goals. *)
Ltac subsolve :=
  ((idtac+symmetry); apply armc_update_reg) ||
  match goal with |- pfsub _ _ =>
      let EQ := fresh "EQ" in let x := fresh "x" in let y := fresh "y" in
      simpl_c; intros x y EQ; try (apply temp_None in EQ|| apply temp_None_L in EQ); c_varx
  end.


Local Ltac etyp' :=
  repeat match goal with
    | H : hastyp_exp ?c ?x ?w0 |- hastyp_exp ?c' (Cast _ _ ?x) _ =>
    eapply TCast with (w:= w0)
    | |- hastyp_exp _ (Cast _ ?c1 (Var (V_TEMP 980))) _ => eapply TCast with (w := 64) (c:=c1)
    | |- hastyp_exp _ (Cast _ ?c1 (Var (V_TEMP 990))) _ => eapply TCast with (w := 64) (c:=c1)
    | |- hastyp_exp _ (R[_,?s]) ?s => unfold arm64_R; cbn
    | |- hastyp_exp _ (SP_read ?s) ?s => unfold SP_read; cbn
    |_: hastyp_exp _ ?x ?s|- hastyp_exp _ (BinOp OP_LT ?x _) _ =>eapply TBinOp with (bop:=OP_LT)
    | |- hastyp_exp _ (BinOp _ (Word _ ?s) _) _ => apply TBinOp with (w := s)
    | |- hastyp_exp _ (BinOp _ _ (Word _ ?s)) _ => apply TBinOp with (w := s)
    | |- hastyp_exp ?c1 (BinOp _ (Var ?v) _) _ => apply TBinOp with (w := sizeof_c c1 v)
    | |- hastyp_exp ?c1 (BinOp _ _ (Var ?v)) _ => apply TBinOp with (w := sizeof_c c1 v)
    | |- hastyp_exp _ (Concat (Word _ ?cw1) (Word _ ?cw2)) _ => apply TConcat with (w1 := cw1) (w2 := cw2)
    | |- hastyp_exp _ (Concat _ _) _ => eapply TConcat
    | |- hastyp_exp _ (BinOp OP_OR _ _) ?sw => eapply TBinOp with (bop :=OP_OR)
    | |- hastyp_exp _ (BinOp ?bop _ _) ?sw => idtac "Apply BinOp "bop" with width "sw ; eapply TBinOp with (w := sw)
    | |- hastyp_exp _ (Cast _ _ (Var (V_TEMP _))) _ => eapply TCast; [apply TVar; reflexivity | try lia]
    | |- hastyp_exp _ (Cast _ _ (Word _ ?sw)) _ => eapply TCast with (w := sw)
    | |- hastyp_exp ?c1 (Cast _ _ (Var ?v)) _ => eapply TCast with (w := sizeof_c c1 v)
    | |- hastyp_exp _ (Cast _ _ (XtoVar _)) _ => eapply TCast with (w := 64)
    | |- hastyp_exp _ (Cast _ _ _) _ => eapply TCast
    | |- hastyp_exp _ (Extract _ _ (XtoVar _)) ?sw => apply TExtract with (w := 64)
    | |- hastyp_exp _ (Extract _ _ _) ?sw => apply TExtract with (w := sw)
    | |- hastyp_exp _ (Var (arm_varid _)) 64 => apply hastyp_arm_varid
    | |- hastyp_exp _ (Var _) _ => apply TVar
    | |- hastyp_exp _ (Ite _ _ _) ?sw => apply TIte with (w := 1)
    | |- hastyp_exp _ (UnOp _ _) _ => apply TUnOp
    | |- hastyp_exp _ (Unknown _) _ => apply TUnknown
    | |- hastyp_exp _ (Word _ _) _ => apply TWord
    | |- hastyp_exp _ (if ?x then _ else _) => destruct x
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
  | H: hastyp_exp empty ?e _ |- hastyp_exp _ ?e _ => apply (hastyp_exp_empty _ _ _ H)
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

  Local Lemma hastyp_havoc:
  forall c,
    armc ⊆ c ->
    hastyp_stmt armc c havoc c.
Proof.
  intros. unfold_stmt. stypc c; now try apply H.
Qed.


Local Ltac e_stypc c :=
  (* Do not simplify the memory bitwidth and massage it into
     the TStore/TLoad format. *)
  cbn -[N.mul N.pow N.shiftl N.shiftr]; rewrite ?(N.mul_comm 8 (2^64));
  repeat match goal with
  | |- hastyp_stmt _ _ (Seq _ _) _ => eapply TSeq
  | |- hastyp_stmt _ _ (If _ _ _) _ => eapply TIf
  | |- hastyp_stmt _ _ (Exn _) _ => apply TExn
  | |- hastyp_stmt _ _ (Rep _ _) _ => eapply TRep
  | |- hastyp_stmt _ _ Nop _ => apply TNop
  | |-hastyp_stmt _ _ havoc _ => eapply hastyp_havoc
  | |- hastyp_stmt _ ?c1 (Move R_NG _) _ => eapply TMove with (w:= 1) (c':= c1); [right; reflexivity | |]
  | |- hastyp_stmt _ ?c1 (Move R_ZR _) _ => eapply TMove with (w:= 1) (c':= c1); [right; reflexivity | |]
  | |- hastyp_stmt _ ?c1 (Move R_CY _) _ => eapply TMove with (w:= 1) (c':= c1); [right; reflexivity | |]
  | |- hastyp_stmt _ ?c1 (Move R_OV _) _ => eapply TMove with (w:= 1) (c':= c1); [right; reflexivity | |]
  | |- hastyp_stmt _ ?c1 (Move (V_TEMP ?v) _) _ =>
      eapply TMove with (c' := update c1 (V_TEMP v) (Some _))
  | |- hastyp_stmt _ ?c1 (Move (arm_varid ?v) _) _ =>
      apply TMove with (w := 64) (c' := c1 ); [right | | ]
  | |- hastyp_stmt _ ?c1 (Move (XtoVar ?v) _) _ => idtac "MATCHED XtoVar" v;
      apply TMove with (w := 64) (c' := c1 )
  | |- hastyp_stmt _ ?c1 (Move ?v _) _ => idtac "MATCHED fallthru" v;
      eapply TMove with (w := sizeof_c c1 v)
      (c' := update c1 (v) (Some _)); [> right | | try apply update_some_c]; try reflexivity
  | |- _ = None \/ _ = Some _ => (left; reflexivity) + (right; reflexivity)
  | |- hastyp_exp _ _ _  => new_etyp
  | |- _ ⊆ _ => try (reflexivity || subsolve)
  | |- Some _ = armc _ => try reflexivity
  | |- _ <= (if ?c then _ else _) => destruct c; try lia
  end.

Local Ltac styp := stypc armc.
Local Ltac estyp := e_stypc armc. (* choice of context has no effect. *)
Local Ltac estyp_c c:= e_stypc c.


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
  destruct (Unpack_NZCV flags) as [[[? z] c0] v] eqn:Hunpack.
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
  forall c n e datasize,
    datasize = 64 \/ datasize = 32 ->
    armc ⊆ c ->
    hastyp_exp armc e datasize ->
    hastyp_stmt armc c (arm_assign_R n e) armc.
Proof.
  intros. unfold arm_assign_R. styp.
  rewrite sizeof_arm_varid. apply typeof_arm_varid.
  rewrite sizeof_arm_varid. eapply TCast.
  apply hastyp_exp_weaken with (c1:= arm8typctx) (c2:= c) (t:=datasize);
  assumption. lia.
  rewrite sizeof_arm_varid. apply typeof_arm_varid. assumption.
Qed.

Local Lemma hastyp_arm_data_il:
  forall c assign assign_flags Rn result flags datasize,
    armc ⊆ c ->
    datasize = 64 \/ datasize = 32 ->
    hastyp_exp armc result datasize ->
    hastyp_exp armc flags 4 ->
    hastyp_stmt armc c (arm_data_il assign assign_flags Rn result flags) armc.
Proof.
  intros. unfold_stmt. destruct assign_flags.
  apply hastyp_arm_assign_flags; assumption.
  destruct assign. eapply hastyp_assign_R with (datasize := datasize); assumption.
  eapply TNop; assumption.
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

Local Lemma hastyp_ShiftC :
forall reg shiftype amount datasize,
(0 < 2 ^ datasize) -> (amount < 2 ^ datasize) ->
(datasize = 32 \/ datasize = 64)->
hastyp_exp arm8typctx
(ShiftC R[ reg, datasize] (DecodeShift shiftype)
<{ {amount} # {datasize} }> datasize) datasize.
Proof.
  intros. unfold ShiftC. destruct_match.
  -
  etyp'. all: try assumption.
  all: destruct H1; subst; psimpl; etyp'.
  all: try unfold sizeof_c. all: try rewrite typeof_arm_varid. all: try (reflexivity||lia).
  -
  etyp'. all: try assumption.
  all: destruct H1; subst; psimpl; etyp'.
  all: try unfold sizeof_c. all: try rewrite typeof_arm_varid. all: try (reflexivity||lia).
  -
  etyp'. all: try assumption.
  all: destruct H1; subst; psimpl; etyp'.
  all: try unfold sizeof_c. all: try rewrite typeof_arm_varid. all: try (reflexivity||lia).
  -
  etyp'. all: try assumption.
  all: destruct H1; subst; psimpl; etyp'.
  all: try unfold sizeof_c. all: try rewrite typeof_arm_varid. all: try (reflexivity||lia).
Qed.


Local Lemma hastyp_ShiftReg :
  forall reg shiftype amount datasize,
  (datasize = 32 \/ datasize = 64)->
  (amount < 2 ^ datasize)->
  hastyp_exp armc (ShiftReg reg (DecodeShift shiftype) <{ {amount} # {datasize} }>
datasize) datasize.
Proof.
  intros. unfold ShiftReg. eapply hastyp_ShiftC; try assumption. lia.
Qed.


Local Lemma hastyp_arm_data_imm:
  forall op sf s sh imm12 Rn Rd,
    imm12 < 2^12 ->
    hastyp_stmt armc armc (arm_data_imm2il op sf s sh imm12 Rn Rd) armc.
Proof.
  intros. unfold_stmt.
  destruct op eqn:?.
  - unfold_stmt. destruct (sf =? 1) eqn:?. destruct (Rn =? 31) eqn:?.
Admitted.

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

Lemma pfsub_remove {A B:Type} {Eq:EqDec A}:
  forall (c:A->option B) v, pfsub (update c v None) c.
Proof.
  intros. intros x y H. destruct (iseq x v).
    subst. rewrite update_updated in H. discriminate.
    rewrite update_frame in H; assumption.
Qed.

Local Lemma scast_bound:
  forall w w' n, scast w w' n < 2^w'.
Proof.
  intros; unfold scast. apply ofZ_bound.
Qed.

Local Lemma hastyp_UsingAArch32:
  forall c (PF:pfsub armc c), hastyp_exp c UsingAArch32 1.
Proof.
  intros; unfold UsingAArch32; etyp. apply PF. reflexivity.
Qed.

Local Ltac etypeasy :=
  apply scast_bound || apply hastyp_UsingAArch32 || ((idtac+symmetry);apply typeof_arm_varid) ||
  match goal with
  | H: pfsub ?c ?c' |- ?c' _ = _ => apply H; try reflexivity
  | |- _ => try repeat (econstructor || assumption || lia || discriminate || reflexivity)
  end.

Local Ltac solve_armc_sub :=
  match goal with
  | |- ?c ⊆ update ?c' ?x (Some ?y) =>
      first
        [ apply update_some;  [ reflexivity||apply typeof_arm_varid | solve_armc_sub ]
        | apply update_fresh2; [ reflexivity | solve_armc_sub ]]
  | |- update ?c _ None ⊆ ?c2 => apply pfsub_remove
  | |- ?c ⊆ ?c2 => reflexivity || assumption
  | H: pfsub armc ?c |- ?c _ = _ => apply H; reflexivity
  end.

Local Ltac solve_armc_sub' :=
  match goal with
  | |- ?c ⊆ update ?c' ?x (Some ?y) =>
      first
        [ apply update_some;  [ (repeat rewrite update_frame in c by etypeasy); try rewrite update_updated; reflexivity || etypeasy
                              | solve_armc_sub ]
        | apply update_fresh2; [ (repeat rewrite update_frame in c by etypeasy); try rewrite update_updated; reflexivity || etypeasy
                              | solve_armc_sub ]
        | ((apply update_some; solve_armc_sub) + (apply update_fresh2; solve_armc_sub))]
  | |- update ?c _ None ⊆ ?c2 => apply pfsub_remove
  | |- ?c ⊆ ?c2 => reflexivity || assumption
  | H: pfsub armc ?c |- ?c _ = _ => apply H; reflexivity
  end.


Local Lemma Replicate_bound:
  forall N0 M x, Replicate N0 M x < 2^N0.
Proof.
  intros.  unfold Replicate. apply N.mod_lt. lia.
Qed.

Local Lemma hastyp_ConditionHolds:
  forall c n (PFSUB: pfsub arm8typctx c),  n<2^4 -> hastyp_exp c (ConditionHolds n) 1.
Proof.
  intros. unfold ConditionHolds.
  destruct_match; etyp; etypeasy; unfold xbits; psimpl; lia.
Qed.

Local Lemma hastyp_XtoVar:
  forall n c (PFSUB: pfsub arm8typctx c), hastyp_exp c (XtoVar n) 64.
Proof.
  intros. unfold XtoVar.
  repeat destruct_match; econstructor; apply PFSUB; reflexivity.
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

Local Lemma hastyp_BranchTo:
  forall c t (T:hastyp_exp c t 64) (PFSUB:pfsub armc c), hastyp_stmt armc c (BranchTo 64 t) c.
Proof.
  intros; unfold BranchTo, UsingAArch32.
  stypc c; etypeasy; try apply lt_pow2_lin || eassumption || reflexivity.
Qed.

Local Lemma hastyp_arm_cbnz2il:
  forall c Xn imm19 (B1:imm19 < 2^21) (B2:Xn<2^5) (PF:pfsub armc c),
  hastyp_stmt armc c (arm_cbnz2il Xn imm19 64) c.
Proof.
  intros. unfold_stmt. estyp; try (reflexivity || lia).
  apply hastyp_XtoVar; assumption.
  apply hastyp_UsingAArch32; assumption.
  styp; etypeasy.
Qed.

Local Lemma hastyp_arm_cbz2il:
  forall c Xn imm19 (B1:imm19 < 2^21) (B2:Xn<2^5) (PF:pfsub armc c),
  hastyp_stmt armc c (arm_cbz2il Xn imm19 64) c.
Proof.
  intros. unfold_stmt. estyp; try (reflexivity || lia).
  apply hastyp_XtoVar; assumption.
  apply hastyp_UsingAArch32; assumption.
  styp; etypeasy.
Qed.

Local Lemma hastyp_arm_br2il:
  forall c (Xn:N) (B:Xn < 2^5) (PF:pfsub armc c), hastyp_stmt armc c (arm_br2il Xn) c.
Proof.
  intros; unfold_stmt. apply hastyp_BranchTo;[apply hastyp_XtoVar|]; assumption.
Qed.

Lemma pfsub_remove2 {A B:Type} {E:EqDec A}:
  forall c1 c2 var (val:B), (forall x y, x<>var -> c1 x = Some y -> c2 x = Some y) -> update c1 var None ⊆ update c2 var (Some val).
Proof.
  intros. intros x y H2. destruct (iseq x var0).
    subst. rewrite update_updated in H2; discriminate.
    rewrite update_frame in * by assumption. apply H; assumption.
Qed.

Local Lemma update_sub :
  forall (c : typctx) (v : N) (w : bitwidth),
    c (arm_varid v) = Some w ->
    c ⊆ update c (arm_varid v) (Some w).
Proof.
  intros c v w H x y H2. destruct (iseq x (arm_varid v)).
    subst; rewrite H2 in H; inversion H; subst. rewrite update_updated. reflexivity.
    rewrite update_frame; assumption.
Qed.



Local Lemma hastyp_arm_blr2il:
  forall c (Xn:N) (B:Xn < 2^5) (PF:pfsub armc c), hastyp_stmt armc c (arm_blr2il Xn) (update c (V_TEMP 1) None).
Proof.
  intros. unfold_stmt. econstructor. estyp_c (update c (V_TEMP 1) None); try apply hastyp_XtoVar; etypeasy. 2: reflexivity.
  econstructor. econstructor. right; cbn; reflexivity. etyp; rewrite update_frame; etypeasy. reflexivity.
  econstructor. apply hastyp_BranchTo. etyp. apply update_some; etypeasy. apply update_fresh2; etypeasy.
  econstructor. 2-3:reflexivity.
  intros x y H.
  destruct (x==arm_varid 30).
    subst. rewrite update_updated, update_frame in *. specialize (PF (arm_varid 30) _ (eq_refl _)). now rewrite PF in H.
    apply armvarid_neq_temp.
    rewrite update_frame; try assumption.
    destruct (x==V_TEMP 1);[subst; discriminate|rewrite update_frame in *; assumption].
Qed.

Local Lemma hastyp_arm_ret2il:
  forall c (Xn:N) (B:Xn < 2^5) (PF:pfsub armc c), hastyp_stmt armc c (arm_ret2il Xn) c.
Proof.
  intros; unfold_stmt. apply hastyp_BranchTo;[etyp|assumption]. apply hastyp_XtoVar; assumption || lia.
Qed.

Definition hastyp_arm_eret2il := hastyp_havoc.
Definition hastyp_arm_drps2il:= hastyp_havoc.
Definition hastyp_arm_braaz2il := hastyp_havoc.
Definition hastyp_arm_braa_reg2il := hastyp_havoc.
Definition hastyp_arm_blraa_reg2il := hastyp_havoc.
Definition hastyp_arm_blraaz2il := hastyp_havoc.
Definition hastyp_arm_retaa2il := hastyp_havoc.
Definition hastyp_arm_eretaa2il := hastyp_havoc.

Local Lemma hastyp_arm_b2il:
  forall c (imm26:N) (B:imm26 < 2^26) (PF:pfsub armc c), hastyp_stmt armc c (arm_b2il imm26) c.
Proof.
  intros; unfold_stmt. styp; etypeasy; apply scast_bound || reflexivity.
Qed.

Local Lemma hastyp_arm_bl2il:
  forall c (imm26:N) (B:imm26<2^26) (PF:pfsub armc c), hastyp_stmt armc c (arm_bl2il imm26) c.
Proof.
  intros; unfold_stmt. econstructor.
  econstructor. right; reflexivity. etyp; etypeasy. eapply (update_some _ _ c). etypeasy. easy.
  styp; etypeasy. reflexivity.
Qed.

Local Lemma hastyp_arm_tbz2il:
  forall c (Rt imm14 b5 b40:N) (B1:Rt<2^5) (B2:imm14<2^14) (B3:b5<2^1) (B4:b40<2^2) (PF:pfsub armc c),
  hastyp_stmt armc c (arm_tbz2il Rt imm14 b5 b40) c.
Proof.
  intros. unfold_stmt. stypc c. eapply hastyp_XtoVar; etypeasy.
  unfold cbits. change 64 with (2^(1+5)); eapply concat_bound; lia. lia.
  all: etypeasy. assumption.
Qed.

Local Lemma hastyp_arm_tbnz2il:
  forall c (Rt imm14 b5 b40:N) (B1:Rt<2^5) (B2:imm14<2^14) (B3:b5<2^1) (B4:b40<2^2) (PF:pfsub armc c),
  hastyp_stmt armc c (arm_tbnz2il Rt imm14 b5 b40) c.
Proof.
  intros. unfold_stmt. stypc c. eapply hastyp_XtoVar; etypeasy.
  unfold cbits. change 64 with (2^(1+5)); eapply concat_bound; lia. lia.
  all: etypeasy. assumption.
Qed.

Local Lemma DecodeBitMasks_bound:
  forall immN imms immr immediate M
    (B1:immN=0\/immN=1) (B2:imms<2^6) (B3:immr<2^6) (B4:M=32\/M=64),
    match DecodeBitMasks immN imms immr immediate M with
    | (w, t) => w<2^M /\ t<2^M
    end.
Proof.
  intros; unfold DecodeBitMasks.
  destruct_match_rmr.
  destruct_match_in e.
  1,2,4: inversion e; subst; lia.
  match type of e with
  | (?a, ?b) = (?n0, ?n1) =>
      assert (H1: n0 = a) by (inversion e; subst; reflexivity);
      assert (H2: n1 = b) by (inversion e; subst; reflexivity);
      subst n0 n1; clear e
  end.
  split; apply Replicate_bound.
Qed.

Local Lemma wmask_bound:
  forall immN imms immr immediate M
    (B1:immN=0\/immN=1) (B2:imms<2^6) (B3:immr<2^6) (B4:M=32\/M=64),
    wmask immN imms immr immediate M < 2^M.
Proof.
  intros; unfold wmask. pose proof (H:=DecodeBitMasks_bound immN imms immr immediate M B1 B2 B3 B4).
  remember (DecodeBitMasks _ _ _ _ _) eqn:Heqp. unfold DecodeBitMasks in Heqp. destruct_match_in Heqp.
  all:subst p; try simpl; try lia.
  apply Replicate_bound.
Qed.

Local Lemma hastyp_wmask:
  forall immN imms immr immediate M
    (B1:immN=0\/immN=1) (B2:imms<2^6) (B3:immr<2^6) (B4:M=32\/M=64),
    hastyp_exp armc (Word (wmask immN imms immr immediate M) M) M.
Proof.
  intros; econstructor. apply wmask_bound; lia.
Qed.

Local Lemma tmask_bound:
  forall immN imms immr immediate M
    (B1:immN=0\/immN=1) (B2:imms<2^6) (B3:immr<2^6) (B4:M=32\/M=64),
    tmask immN imms immr immediate M < 2^M.
Proof.
  intros; unfold tmask. pose proof (H:=DecodeBitMasks_bound immN imms immr immediate M B1 B2 B3 B4).
  remember (DecodeBitMasks _ _ _ _ _) eqn:Heqp. unfold DecodeBitMasks in Heqp. destruct_match_in Heqp.
  all:subst p; try simpl; try lia.
  apply Replicate_bound.
Qed.

Local Lemma hastyp_tmask:
  forall immN imms immr immediate M
    (B1:immN=0\/immN=1) (B2:imms<2^6) (B3:immr<2^6) (B4:M=32\/M=64),
    hastyp_exp armc (Word (tmask immN imms immr immediate M) M) M.
Proof.
  intros; econstructor. apply tmask_bound; lia.
Qed.

Local Lemma hastyp_ExtendReg:
  forall c regt regn exttype shift (PF:pfsub armc c) (B1:regn<2^5) (B2:shift<2^3) (B3:exttype<2^3),
  hastyp_stmt armc c (ExtendReg (V_TEMP regt) regn exttype shift) (update c (V_TEMP regt) (Some 64)).
Proof.
  intros. unfold ExtendReg.
  econstructor. estyp;(lia || reflexivity).
  remember (N.min _ _) as min. econstructor. etyp;lia. estyp; try lia. apply hastyp_XtoVar; assumption.
  all: try reflexivity.
  assert (min <= 64). { rewrite Heqmin, N.min_le_iff. right. lia.  }
  estyp; try lia.
  apply hastyp_XtoVar; etypeasy.
Qed.

Local Lemma hastyp_ExtendReg':
  forall c wout reg exttype shift (PF:pfsub armc c) (B1:reg<2^5) (B2:shift<2^3) (B3:exttype<2^3) (B4:8<wout<=64),
  hastyp_exp c (ExtendReg' wout reg exttype shift) wout.
Proof.
  intros. unfold ExtendReg'.
  destruct_match; econstructor; try etyp; try lia.
  econstructor. econstructor. apply hastyp_XtoVar; assumption. lia.
  apply N.le_lt_trans with (m:=wout-shift-1); try lia.
  lia.
  repeat econstructor. apply hastyp_XtoVar; assumption.
  all: lia.
Qed.



Local Ltac c_var :=
  repeat rewrite update_frame by discriminate;
  match goal with H: pfsub armc ?c |- ?c _ = _ => apply H; reflexivity end.

Local Ltac solve_TagAligned :=
  apply hastyp_AlignCheck; lia || etyp || solve_armc_sub; c_var.






Local Lemma hastyp_sp_xn:
  forall Xn, hastyp_exp arm8typctx (if Xn =? 31 then Var R_SP else <{ X[ {Xn}] }>) 64.
Proof.
  intros. destruct_match.
    etyp. apply hastyp_XtoVar. reflexivity.
Qed.

Local Lemma hastyp_RORExp:
  forall w x shift
    (B1:shift<2^w) (B2:hastyp_exp armc x w),
    hastyp_exp armc (RORExp w x shift) w.
Proof.
  intros; unfold RORExp.
  etyp'. all: assumption || lia || apply lt_pow2_lin.
Qed.

(* Try to solve a hastyp_exp goal, dealing with fairly complex context subset subgoals. *)
(* casesolve tries esolve and other things.  To break the circular dependency we parameterize
   casesolve on a guarding tactic---idtac or failure.  esolve calls it with failure so
   to prevent casesolve calling it recursively. *)
Local Ltac casesolve_ p := idtac.
Local Ltac esolve :=
  simpl_c; etyp;
  (apply hastyp_XtoVar
    || apply hastyp_b2exp
    || apply hastyp_AlignCheck
    || apply hastyp_ExtendReg'
    || apply hastyp_sp_xn
    || apply hastyp_RORExp
    || apply hastyp_Pack_NZCV
    || apply hastyp_ConditionHolds
    || apply hastyp_Ones
    || idtac
  ); (try casesolve_ fail); try etypeasy; try solve_armc_sub; try c_var; try c_varx.


Local Lemma hastyp_check:
  forall Xn, hastyp_stmt armc armc (if Xn =? 31 then CheckSPAlignment else <{ nop }>) armc.
Proof.
  intros. destruct_match. apply hastyp_CheckSPAlignment; reflexivity.
  econstructor; reflexivity.
Qed.

(* Try to solve a hastyp_stmt goal using aux-function lemmas. *)
Local Ltac ssolve H :=
    apply H
    || apply hastyp_havoc
    || apply hastyp_CheckSPAlignment
    || apply hastyp_BranchTo
    || apply hastyp_ExtendReg
    || apply hastyp_check
    (*|| apply Replicate_bound*)
    || apply hastyp_wmask || apply hastyp_tmask
    || estyp.

Ltac destruct_oreq :=
  try match goal with
  | H: ?x = _ \/ _ |- context[?x] => destruct H; subst
  end.

Ltac casesolve_ tryesolve ::=
  assumption
  (* Apply specific reflexivity lemmas.  Using [reflexivity] binds the evar in, e.g., [?w <= 64]
     leading to unprovable goals. *)
  || apply pfsub_refl || apply eq_refl
  (* Subfunctions for DecodeBitMasks users (e.g. UBFM). *)
  || (apply wmask_bound;lia) || (apply tmask_bound; lia)
  (* Some functions take the minimum of two values. *)
  || (apply N.min_le_iff; first [left;lia | right;lia])
  (* For N.shiftl 1 size <= 64 goals *)
  || (rewrite ?N.shiftl_mul_pow2, ?N.shiftr_div_pow2; try destruct_oreq; lia)
  (* armc _ = None \/ armc _ = Some _ *)
  || first [left;reflexivity | right;(reflexivity || (idtac+symmetry);apply typeof_arm_varid)]
  (* pfsub *)
  || subsolve
  (* hastyp_exp *)
  || (tryif tryesolve then esolve else idtac)
  (* context x = Some _ *)
  || cget.

Tactic Notation "casesolve" := casesolve_ idtac.

(* Step through a hastyp_stmt proof, solving trivially solvable cases. *)
Ltac econs_ H :=
  (* econstructor by default, but prefer special cases for TLoad and TStore
     to unify the memory bitwidth early and allow the solvers to solve the other
     goals. *)
  (  (eapply TCast;[econs_ H|])
    || (eapply TLoad;[|etyp;casesolve|])
    || (eapply TStore;[|etyp;casesolve| | ])
    || econstructor
    || (rewrite N.mul_comm; econstructor));
  simpl_c; repeat destruct_match_rmr;
  try solve [(try ssolve H); (casesolve || (try destruct_oreq; repeat (try etyp; casesolve)))].

(* `econs with H` gives econs a hint of how to solve subgoals after its
   econstructor step. *)
Tactic Notation "econs" "with" reference(h) := econs_ h.
Tactic Notation "econs" := econs_ I.

(* For solving fetching a register out of a big context.  E.g.,
  (c[temp[ 1000] := Some 64][temp[ 2000] := Some (N.shiftl 1 scale * 8)]
  [temp[ 3000] := Some (N.shiftl 1 scale * 8)][temp[ 2000] := Some (N.shiftl 8 scale)]
  [temp[ 3000] := Some (N.shiftl 8 scale)][<{ var[ {Xt}] }> := Some 64]
  [<{ var[ {Xt2}] }> := Some 64]) <{ var[ {Xn}] }> =
    Some 64 *)
Ltac c_var_reg :=
repeat match goal with
|- update ?c ?v ?val ?x = Some _ =>
    (rewrite update_updated; reflexivity)
    || (rewrite update_frame by (discriminate||((idtac+symmetry); apply armvarid_neq_temp)))
    || (let EQ:=fresh "EQ" in destruct (x==v) as [EQ | ?];[rewrite <-EQ in *; rewrite update_updated; reflexivity | rewrite update_frame by assumption ])
| PF: pfsub armc ?c |- ?c _ = Some _ => apply PF; try (reflexivity || apply typeof_arm_varid)
end.

Local Ltac simple_c_var :=
  (idtac+symmetry);
    (repeat match goal with
    | |- update ?c (arm_varid ?v) _ (arm_varid ?x) = _ =>
        let EQ := fresh "EQ" in
        destruct (arm_varid x == arm_varid v) as [EQ | ?];[
            rewrite <-EQ,update_updated in *; clear EQ; try reflexivity
            | rewrite update_frame by assumption
            ]
    | |- _ => rewrite !update_frame by
          ((intros;discriminate) || (idtac+symmetry);(apply armvarid_neq_temp || apply armvarid_neq_mem))
    end);
    match goal with
    | PF: pfsub armc ?c |- ?c _ = _ => apply PF, typeof_arm_varid
    | |- armc _ = _ => reflexivity
    end.
    (*rewrite !update_frame by (apply armvarid_neq_temp || apply armvarid_neq_mem); *)
    (*match goal with*)
    (*| PF: pfsub armc ?c |- ?c _ = _ => apply PF, typeof_arm_varid*)
    (*end.*)

Tactic Notation "unfold" "left" "in" hyp(H) :=
  match type of H with
  | _ ?l _ => revert H; unfold_rec l; intros H
  end.

Tactic Notation "unfold" "right" "in" hyp(H) :=
  match type of H with
  | _ _ ?r => revert H; unfold_rec r; intros H
  end.

Local Ltac split_cases :=
  repeat match goal with
         | H: _ \/ _ |- _ => destruct H
         | b:bool |- _ => destruct b
         end;
  subst; destruct_match.

Local Lemma unsome_ {A:Type}:
  forall (a b:A), Some a = Some b -> a = b.
Proof. intros a b H; inversion H; subst; reflexivity. Qed.

Tactic Notation "unsome" hyp(H) :=
  apply unsome_ in H.

Local Lemma hastyp_arm_stxr2il_constr:
  forall (size Xn Xs Xt:N) (rtunknown rnunknown:bool)
  (B1:Xn<2^5) (B2:Xs<2^5) (B3:Xt<2^5) (B4:size<=64),
  hastyp_stmt armc armc (arm_stxr2il_constr size Xn Xs Xt rtunknown rnunknown) armc.
Proof.
  intros. unfold_stmt. destruct_match.
  (*all: repeat econs.*)
  (*all: solve_armc_sub.*)
(*Qed.*)
Admitted.

Local Ltac esolve' :=
  repeat (lia || solve_armc_sub || ((left + right); reflexivity) || econstructor || etyp).
Local Lemma hastyp_arm_stxr2il_size:
  forall (size Xn Xs Xt:N)
  (B1:Xn<2^5) (B2:Xs<2^5) (B3:Xt<2^5) (B4:size<=64) (B5:N.shiftr size 3 * 8 = size) ,
  hastyp_stmt armc armc (arm_stxr2il_size size Xn Xs Xt) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  all: try apply hastyp_arm_stxr2il_constr; esolve'.
Qed.

(* TODO retype the updated *_constr definitions and the instructions that use them. *)
Local Lemma hastyp_arm_stxp2il_constr:
  forall (size Xn Xs Xt Xt2:N) (rtunknown rnunknown:bool)
  (B1:Xn<2^5) (B2:Xs<2^5) (B3:Xt<2^5) (B4:size<=64) (B5:Xt2<2^5),
  hastyp_stmt armc armc (arm_stxp2il_constr size Xn Xs Xt Xt2 rtunknown rnunknown) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  (*all: repeat econs.*)
  (*all: solve_armc_sub.*)
(*Qed.*)
Admitted.

Local Lemma hastyp_arm_stxp2il_size:
  forall (size Xn Xs Xt Xt2:N) (rtunknown rnunknown:exp)
  (B1:Xn<2^5) (B2:Xs<2^5) (B3:Xt<2^5) (B4:size<=64) (B5:Xt2<2^5) (B6:N.shiftr size 3 * 8 = size),
  hastyp_stmt armc armc ((arm_stxp2il_size size Xn Xs Xt Xt2)) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  all: try apply hastyp_arm_stxp2il_constr; esolve'.
Qed.

Local Lemma hastyp_arm_ldxp2il_constr:
  forall (size Xn Xt Xt2:N) (rtunknown:bool)
  (B1:Xn<2^5) (B3:Xt<2^5) (B4:size=8\/size=16\/size=32\/size=64) (B5:Xt2<2^5) ,
  hastyp_stmt armc armc (arm_ldxp2il_constr size Xn Xt Xt2 rtunknown) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  (*all: repeat econs.*)
  (*all: solve_armc_sub.*)
(*Qed.*)
Admitted.

Local Lemma hastyp_arm_ldxp2il_size:
  forall (size Xn Xt Xt2:N) (rtunknown:bool)
  (B1:Xn<2^5) (B3:Xt<2^5) (B4:size=8\/size=16\/size=32\/size=64) (B5:Xt2<2^5) ,
  hastyp_stmt armc armc ((arm_ldxp2il size Xn Xt Xt2)) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  all: try apply hastyp_arm_ldxp2il_constr; esolve'.
Qed.

Local Lemma hastyp_arm_ldnp2il_constr:
  forall Xn Xt Xt2 imm7 scale rtunknown
  (B1:Xn<2^5) (B3:Xt<2^5) (B5:Xt2<2^5) (B2:imm7<2^7) (B4:scale=2\/scale=3),
  hastyp_stmt armc armc (arm_ldnp2il_constr Xn Xt Xt2 imm7 scale rtunknown) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  (*all: time repeat econs.*)
  (*all: solve_armc_sub.*)
(*Qed.*)
Admitted.

Local Lemma hastyp_arm_ldnp2il:
  forall Xn Xt Xt2 imm7 scale
  (B1:Xn<2^5) (B3:Xt<2^5) (B5:Xt2<2^5) (B2:imm7<2^7) (B4:scale=2\/scale=3) ,
  hastyp_stmt armc armc ((arm_ldnp2il Xn Xt Xt2 imm7 scale)) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  all: try apply hastyp_arm_ldnp2il_constr; esolve'.
Qed.

Local Lemma hastyp_arm_stp2il_constr:
  forall Xn Xt Xt2 imm7 scale wback (postindex:bool) rtunknown
  (B1:Xn<2^5) (B3:Xt<2^5) (B5:Xt2<2^5) (B2:imm7<2^7) (B4:scale=2\/scale=3),
  hastyp_stmt armc armc (arm_stp2il_constr Xn Xt Xt2 imm7 scale wback postindex rtunknown) armc.
Proof.
  intros; unfold_stmt; destruct_match.
  (*all: time repeat econs. (* 33.52s *)*)
  (*all: try solve_armc_sub.*)
(*Qed.*)
Admitted.

Local Lemma hastyp_arm_stp2il:
  forall Xn Xt Xt2 imm7 scale wback (postindex:bool)
  (B1:Xn<2^5) (B3:Xt<2^5) (B5:Xt2<2^5) (B2:imm7<2^7) (B4:scale=2\/scale=3) ,
  hastyp_stmt armc armc ((arm_stp2il Xn Xt Xt2 imm7 scale wback postindex)) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  all: try apply hastyp_arm_stp2il_constr; esolve'.
Qed.

Local Lemma hastyp_arm_ldp2il_constr:
  forall Xn Xt Xt2 imm7 scale wback wb_unknown rt_unknown postindex
  (B1:Xn<2^5) (B3:Xt<2^5) (B5:Xt2<2^5) (B6:imm7<2^7) (B7:scale=2\/scale=3),
  hastyp_stmt armc armc (arm_ldp2il_constr Xn Xt Xt2 imm7 scale wback wb_unknown rt_unknown postindex) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  (*all: time repeat econs. (* 7.17s *)*)
  (*all: solve_armc_sub.*)
(*Qed.*)
Admitted.

Local Lemma hastyp_arm_ldp2il:
  forall Xn Xt Xt2 imm7 scale wback postindex
  (B1:Xn<2^5) (B3:Xt<2^5) (B5:Xt2<2^5) (B6:imm7<2^7) (B7:scale=2\/scale=3) ,
  hastyp_stmt armc armc ((arm_ldp2il Xn Xt Xt2 imm7 scale wback postindex)) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  all: try apply hastyp_arm_ldp2il_constr; esolve'.
Qed.

Local Lemma hastyp_arm_ldpsw2il_constr:
  forall Xn Xt Xt2 imm7 wback wb_unknown rt_unknown postindex
  (B1:Xn<2^5) (B3:Xt<2^5) (B4:imm7<2^7) (B5:Xt2<2^5),
  hastyp_stmt armc armc (arm_ldpsw2il_constr Xn Xt Xt2 imm7 wback wb_unknown rt_unknown postindex) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  (*all: time repeat econs. (* 10.67s *)*)
  (*all: esolve'.*)
(*Qed.*)
Admitted.

Local Lemma hastyp_arm_ldpsw2il:
  forall Xn Xt Xt2 imm7 wback postindex
  (B1:Xn<2^5) (B3:Xt<2^5) (B4:imm7<2^7) (B5:Xt2<2^5),
  hastyp_stmt armc armc ((arm_ldpsw2il Xn Xt Xt2 imm7 wback postindex)) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  all: try apply hastyp_arm_ldpsw2il_constr; esolve'.
Qed.

Local Lemma hastyp_arm_str_imm2il_size_constr:
  forall size (Xn Xt imm912:N) (signed wback postindex rtunknown:bool)
  (B1:Xn<2^5)  (B3:Xt<2^5) (B4:if signed then imm912<2^9 else imm912<2^12) (B5:size=8\/size=16\/size=32\/size=64)
  (B6: N.shiftr size 3 * 8 = size),
  hastyp_stmt armc armc (arm_str_imm2il_size_constr size Xn Xt imm912 signed wback postindex rtunknown) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  (*all: time repeat econs. (* 13.12s *)*)
  (*all: esolve'.*)
(*Qed.*)
Admitted.

Local Lemma hastyp_arm_str_imm2il_size:
  forall size (Xn Xt imm912:N) (signed wback postindex rtunknown:bool)
  (B1:Xn<2^5)  (B3:Xt<2^5) (B4:if signed then imm912<2^9 else imm912<2^12) (B5:size=8\/size=16\/size=32\/size=64)
  (B6: N.shiftr size 3 * 8 = size),
  hastyp_stmt armc armc (arm_str_imm2il_size size Xn Xt imm912 signed wback postindex) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  all: try apply hastyp_arm_str_imm2il_size_constr; esolve'.
  all: assumption.
Qed.

Definition hastyp_arm_str_imm2il := hastyp_arm_str_imm2il_size.
Definition hastyp_arm_strb_imm2il := hastyp_arm_str_imm2il_size 8.
Definition hastyp_arm_strh_imm2il := hastyp_arm_str_imm2il_size 16.


Local Lemma hastyp_arm_ldr_imm2il_size_constr:
  forall size (Xn Xt imm912:N) (signed wback postindex wbunknown:bool)
  (B1:Xn<2^5)  (B3:Xt<2^5) (B4:if signed then imm912<2^9 else imm912<2^12) (B5:size=32\/size=64),
  hastyp_stmt armc armc (arm_ldr_imm2il_size_constr size Xn Xt imm912 signed wback postindex wbunknown) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  (*all: time repeat econs. (* 6.31s *)*)
(*Qed.*)
Admitted.

Local Lemma hastyp_arm_ldr_imm2il_size:
  forall size (Xn Xt imm912:N) (signed wback postindex wbunknown:bool)
  (B1:Xn<2^5) (B3:Xt<2^5) (B4:if signed then imm912<2^9 else imm912<2^12) (B5:size=32\/size=64),
  hastyp_stmt armc armc (arm_ldr_imm2il_size size Xn Xt imm912 signed wback postindex) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  all: try apply hastyp_arm_ldr_imm2il_size_constr; esolve'.
  all: assumption.
Qed.

Definition hastyp_arm_ldr_imm2il := hastyp_arm_ldr_imm2il_size.
Definition hastyp_arm_ldrb_imm2il := hastyp_arm_ldr_imm2il_size 8.
Definition hastyp_arm_ldrh_imm2il := hastyp_arm_ldr_imm2il_size 16.

Local Lemma hastyp_arm_ldrs_imm2il_size_constr:
  forall size w' (Xn Xt imm912:N) (signed wback postindex wbunknown:bool)
  (B1:Xn<2^5) (B3:Xt<2^5) (B4:if signed then imm912<2^9 else imm912<2^12) (B5:w'=32\/w'=64) (B6:size=8\/size=16\/size=32),
  hastyp_stmt armc armc (arm_ldrs_imm2il_size_constr size w' Xn Xt imm912 signed wback postindex wbunknown) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  (*all: time repeat econs. (* 9.23s *)*)
(*Qed.*)
Admitted.

Local Lemma hastyp_arm_ldrs_imm2il_size:
  forall size w' (Xn Xt imm912:N) (signed wback postindex:bool)
  (B1:Xn<2^5) (B3:Xt<2^5) (B4:if signed then imm912<2^9 else imm912<2^12) (B5:w'=32\/w'=64) (B6:size=8\/size=16\/size=32),
  hastyp_stmt armc armc (arm_ldrs_imm2il_size size w' Xn Xt imm912 signed wback postindex) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  all: try apply hastyp_arm_ldrs_imm2il_size_constr; esolve'.
  all: assumption.
Qed.

Definition hastyp_arm_ldrsb_imm2il := hastyp_arm_ldrs_imm2il_size 8.
Definition hastyp_arm_ldrsh_imm2il := hastyp_arm_ldrs_imm2il_size 16.
Definition hastyp_arm_ldrsw_imm2il := hastyp_arm_ldrs_imm2il_size 32 64.

Local Lemma hastyp_arm_ldraa2il_constr:
  forall (Xn Xt S imm9:N) (wback wbunknown:bool)
  (B1:Xn<2^5)  (B3:Xt<2^5) (B4:S<2^1) (B5:imm9<2^9),
  hastyp_stmt armc armc (arm_ldraa2il_constr Xn Xt S imm9 wback wbunknown) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  (*all: time repeat econs. (* 1.70s *)*)
(*Qed.*)
Admitted.

Local Lemma hastyp_arm_ldraa2il:
  forall (Xn Xt S imm9:N) (wback:bool)
  (B1:Xn<2^5) (B3:Xt<2^5) (B4:S<2^1) (B5:imm9<2^9),
  hastyp_stmt armc armc (arm_ldraa2il Xn Xt S imm9 wback) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  all: try apply hastyp_arm_ldraa2il_constr; esolve'.
Qed.

Local Lemma hastyp_arm_ldr_reg2il_size_signed:
  forall size signed w' S Xn Xm Xt extend
  (B1:Xn<2^5) (B2:Xm<2^5) (B3:Xt<2^5) (B4:extend<2^3) (B5:w'=32\/w'=64)
  (B6:size=8\/size=16\/size=32\/size=64) (B7:S=0\/S=1) (B8:w'<=size)
  (B9:(size=?64)&&signed=false),
  hastyp_stmt armc armc (arm_ldr_reg2il_size_signed size signed w' S Xn Xm Xt extend) armc.
Proof.
  intros; unfold_stmt. remember ((size=?64)||(w'=?64)) as upcast. split_cases.
  (*all: try (exfalso; lia).*)
  (*all: time repeat econs. (* 1.86s *)*)
(*Qed.*)
Admitted.

Definition hastyp_arm_ldrb_reg2il := hastyp_arm_ldr_reg2il_size_signed 8 false 0 0.
Definition hastyp_arm_ldrh_reg2il := hastyp_arm_ldr_reg2il_size_signed 16 false 0 0.
Definition hastyp_arm_ldr_reg2il size := hastyp_arm_ldr_reg2il_size_signed size false 0.

Definition hastyp_arm_ldrsb_reg2il := hastyp_arm_ldr_reg2il_size_signed 8 true.
Definition hastyp_arm_ldrsh_reg2il := hastyp_arm_ldr_reg2il_size_signed 16 true.
Definition hastyp_arm_ldrsw_reg2il := hastyp_arm_ldr_reg2il_size_signed 32 true 64.

Local Lemma hastyp_arm_str_reg2il_size:
  forall size S c Xn Xm Xt extend
  (B1:Xn<2^5) (B2:Xm<2^5) (B3:Xt<2^5) (B4:extend<2^3) (B5:S<2^3) (PF:pfsub armc c)
  (B6:size=8\/size=16\/size=32\/size=64),
  hastyp_stmt armc c (arm_str_reg2il_size size S Xn Xm Xt extend ) armc.
Proof.
  intros; unfold_stmt. split_cases.
  (*all: time repeat econs. (* 1.14s *)*)
(*Qed.*)
Admitted.


Definition hastyp_arm_strb_reg2il := hastyp_arm_str_reg2il_size 8 0.
Definition hastyp_arm_strh_reg2il := hastyp_arm_str_reg2il_size 16 0.
Definition hastyp_arm_str_reg2il := hastyp_arm_str_reg2il_size.


Definition hastyp_arm_prfm_lit2il  := hastyp_havoc.

Local Lemma hastyp_arm_stlur2il_size:
  forall size Xn Xm Xt imm9 (B1:Xn<2^5) (B2:Xm<2^5) (B3:Xt<2^5) (B4:imm9<2^9)
  (B5:size=8\/size=16\/size=32\/size=64),
  hastyp_stmt armc armc (arm_stlur2il_size size Xn Xt imm9) armc.
Proof.
  (*intros; unfold_stmt. destruct_match. all: repeat econs; solve_armc_sub.*)
(*Qed.*)
Admitted.

Definition hastyp_arm_stlurb2il := hastyp_arm_stlur2il_size 8.
Definition hastyp_arm_stlurh2il := hastyp_arm_stlur2il_size 16.
Definition hastyp_arm_stlur2il := hastyp_arm_stlur2il_size.

Local Lemma hastyp_arm_ldapur2il_size_signed:
  forall size signed w' Xn Xt imm9 (B1:Xn<2^5) (B3:Xt<2^5) (B4:imm9<2^9)
  (B9:(size=?64)&&signed=false)
  (B6:w'=32\/w'=64) (B7:size=8\/size=16\/size=32\/size=64),
  hastyp_stmt armc armc (arm_ldapur2il_size_signed size signed w' Xn Xt imm9) armc.
Proof.
  (*intros; unfold_stmt. remember (size=?64) as upcast. destruct_match. all: time repeat econs.*)
  (*all: symmetry in Hequpcast; rewrite N.eqb_eq in *; subst; repeat econs.*)
  (*all: lia.*)
(*Qed.*)
Admitted.

Definition hastyp_arm_ldapurb2il := hastyp_arm_ldapur2il_size_signed 8 false 0.
Definition hastyp_arm_ldapurh2il := hastyp_arm_ldapur2il_size_signed 16 false 0.
Definition hastyp_arm_ldapurw2il := hastyp_arm_ldapur2il_size_signed 32 false 0.
Definition hastyp_arm_ldapur2il size := hastyp_arm_ldapur2il_size_signed size false 0.

Definition hastyp_arm_ldapursb2il := hastyp_arm_ldapur2il_size_signed 8 true.
Definition hastyp_arm_ldapursh2il := hastyp_arm_ldapur2il_size_signed 16 true.
Definition hastyp_arm_ldapursw2il := hastyp_arm_ldapur2il_size_signed 32 true.


Local Lemma hastyp_arm_stur2il_size:
  forall size Xn Xt imm9 (B1:Xn<2^5) (B3:Xt<2^5) (B4:imm9<2^9)
  (B7:size=8\/size=16\/size=32\/size=64),
  hastyp_stmt armc armc (arm_stur2il_size size Xn Xt imm9) armc.
Proof.
  (*intros; unfold_stmt. destruct_match. all: time repeat econs.*)
  (*all: solve_armc_sub.*)
(*Qed.*)
Admitted.

Definition hastyp_arm_sturb2il := hastyp_arm_stur2il_size 8.
Definition hastyp_arm_sturh2il := hastyp_arm_stur2il_size 16.
Definition hastyp_arm_stur2il := hastyp_arm_stur2il_size.


Local Lemma hastyp_arm_ldur2il_size:
  forall size signed w' Xn Xt imm9 (B1:Xn<2^5) (B3:Xt<2^5) (B4:imm9<2^9)
  (B10:w'=32\/w'=64) (B7:size=8\/size=16\/size=32\/size=64) (B8:w'<=size)
  (B6: N.shiftr size 3 * 8 = size)
  (B9:(size=?64)&&signed=false),
  hastyp_stmt armc armc (arm_ldur2il_size size signed w' Xn Xt imm9) armc.
Proof.
  intros; unfold_stmt. remember (_||_) as u.
  (*split_cases. all: try lia || discriminate.*)
  (*all: time repeat econs.*)
(*Qed.*)
Admitted.

Definition hastyp_arm_ldurb2il := hastyp_arm_ldur2il_size 8 false 0.
Definition hastyp_arm_ldurh2il := hastyp_arm_ldur2il_size 16 false 0.
Definition hastyp_arm_ldur2il size := hastyp_arm_ldur2il_size size false 0.

Definition hastyp_arm_ldursb2il := hastyp_arm_ldur2il_size 8 true.
Definition hastyp_arm_ldursh2il := hastyp_arm_ldur2il_size 16 true.
Definition hastyp_arm_ldursw2il := hastyp_arm_ldur2il_size 32 true 64.

Local Lemma hastyp_MemAtomic:
  forall c op w value address rettemp
    (B2:hastyp_exp c address 64) (B3:w=8\/w=16\/w=32\/w=64) (B4:hastyp_exp c value w)
    (PF:pfsub armc c) (PF':c (V_TEMP rettemp) = None),
  hastyp_stmt armc c (MemAtomic op w value address rettemp) (update c (V_TEMP rettemp) (Some w)).
Proof.
  (*intros; unfold_stmt. destruct_match. all: repeat econs.*)
  (*all: try solve [eapply hastyp_exp_weaken;[eassumption|subsolve]].*)
  (*all: replace (8*N.shiftr w 3) with w by lia.*)
  (*all: replace (N.shiftr w 3*8) with w by lia.*)
  (*all: etyp.*)
  (*all: try solve [eapply hastyp_exp_weaken;[eassumption|subsolve]].*)
  (*all: try match goal with |- hastyp_exp _ <{load[_,_]}> ?w => replace w with (N.shiftr w 3 * 8) at 3 by lia; repeat econs;*)
  (*         eapply hastyp_exp_weaken;[eassumption|subsolve] end.*)
  (*all:try subsolve.*)
  (*all:lia.*)
(*Qed.*)
Admitted.

Local Lemma hastyp_arm_ldatomic2il_size:
  forall op size Xn Xs Xt
  (B2:Xn<2^5) (B3:Xs<2^5) (B4:Xt<2^5) (B5:size=8\/size=16\/size=32\/size=64),
  hastyp_stmt armc armc (arm_ldatomic2il_size op size Xn Xs Xt) armc.
Proof.
  (*intros; unfold_stmt. destruct_match. *)
  (*econs. econs. eapply hastyp_stmt_weaken'. apply hastyp_MemAtomic; try casesolve. solve_armc_sub.*)
  (*econs. econs. eapply hastyp_stmt_weaken'. apply hastyp_MemAtomic; try casesolve. solve_armc_sub.*)
  (*  econs. solve_armc_sub.*)
  (*econs. econs. eapply hastyp_stmt_weaken'. apply hastyp_MemAtomic; try casesolve. solve_armc_sub.*)
  (*econs. econs. eapply hastyp_stmt_weaken'. apply hastyp_MemAtomic; try casesolve. solve_armc_sub.*)
  (*  econs. solve_armc_sub.*)
(*Qed.*)
Admitted.

Definition hastyp_arm_ldaddb2il := hastyp_arm_ldatomic2il_size MemAtomicOp_ADD 8.
Definition hastyp_arm_ldaddh2il := hastyp_arm_ldatomic2il_size MemAtomicOp_ADD 16.
Definition hastyp_arm_ldadd2il := hastyp_arm_ldatomic2il_size MemAtomicOp_ADD.

Definition hastyp_arm_ldumaxb2il := hastyp_arm_ldatomic2il_size MemAtomicOp_UMAX 8.
Definition hastyp_arm_ldumaxh2il := hastyp_arm_ldatomic2il_size MemAtomicOp_UMAX 16.
Definition hastyp_arm_ldumax2il := hastyp_arm_ldatomic2il_size MemAtomicOp_UMAX.

Definition hastyp_arm_lduminb2il := hastyp_arm_ldatomic2il_size MemAtomicOp_UMIN 8.
Definition hastyp_arm_lduminh2il := hastyp_arm_ldatomic2il_size MemAtomicOp_UMIN 16.
Definition hastyp_arm_ldumin2il := hastyp_arm_ldatomic2il_size MemAtomicOp_UMIN.

Definition hastyp_arm_ldsmaxb2il := hastyp_arm_ldatomic2il_size MemAtomicOp_SMAX 8.
Definition hastyp_arm_ldsmaxh2il := hastyp_arm_ldatomic2il_size MemAtomicOp_SMAX 16.
Definition hastyp_arm_ldsmax2il := hastyp_arm_ldatomic2il_size MemAtomicOp_SMAX.

Definition hastyp_arm_ldsminb2il := hastyp_arm_ldatomic2il_size MemAtomicOp_SMIN 8.
Definition hastyp_arm_ldsminh2il := hastyp_arm_ldatomic2il_size MemAtomicOp_SMIN 16.
Definition hastyp_arm_ldsmin2il := hastyp_arm_ldatomic2il_size MemAtomicOp_SMIN.

Definition hastyp_arm_ldclrb2il := hastyp_arm_ldatomic2il_size MemAtomicOp_BIC 8.
Definition hastyp_arm_ldclrh2il := hastyp_arm_ldatomic2il_size MemAtomicOp_BIC 16.
Definition hastyp_arm_ldclr2il := hastyp_arm_ldatomic2il_size MemAtomicOp_BIC.

Definition hastyp_arm_ldsetb2il := hastyp_arm_ldatomic2il_size MemAtomicOp_ORR 8.
Definition hastyp_arm_ldseth2il := hastyp_arm_ldatomic2il_size MemAtomicOp_ORR 16.
Definition hastyp_arm_ldset2il := hastyp_arm_ldatomic2il_size MemAtomicOp_ORR.

Definition hastyp_arm_ldeorb2il := hastyp_arm_ldatomic2il_size MemAtomicOp_EOR 8.
Definition hastyp_arm_ldeorh2il := hastyp_arm_ldatomic2il_size MemAtomicOp_EOR 16.
Definition hastyp_arm_ldeor2il := hastyp_arm_ldatomic2il_size MemAtomicOp_EOR.


Local Lemma hastyp_arm_swp2il_size:
  forall size op Xn Xs Xt
  (B1:op<2^5) (B2:Xn<2^5) (B3:Xs<2^5) (B4:Xt<2^5) (B5:size=8\/size=16\/size=32\/size=64),
  hastyp_stmt armc armc (arm_swp2il_size size Xn Xs Xt) armc.
Proof.
  intros; unfold_stmt. destruct_match.
  (*all: time repeat econs.*)
  (*all: solve_armc_sub.*)
(*Qed.*)
Admitted.

Definition hastyp_arm_swpb2il := hastyp_arm_swp2il_size 8.
Definition hastyp_arm_swph2il := hastyp_arm_swp2il_size 16.
Definition hastyp_arm_swp2il := hastyp_arm_swp2il_size.

Local Lemma hastyp_arm_ldapr2il_size:
  forall size Xn Xt (B1:Xn<2^5) (B2:Xt<2^5) (B3:size=8\/size=16\/size=32\/size=64),
  hastyp_stmt armc armc (arm_ldapr2il_size size Xn Xt) armc.
Proof.
(*  intros; unfold_stmt. destruct_match; repeat econs.*)
(*Qed.*)
Admitted.

Definition hastyp_arm_ldaprb2il := hastyp_arm_ldapr2il_size 8.
Definition hastyp_arm_ldaprh2il := hastyp_arm_ldapr2il_size 16.
Definition hastyp_arm_ldapr2il := hastyp_arm_ldapr2il_size.

Lemma varid_neq_temp :
 forall v a, <{ var[ {v} ] }> <> (V_TEMP a).
Proof.
  intros. unfold arm_varid. destruct v; try discriminate.
  repeat (destruct p; try discriminate).
Qed.

Ltac match_awcs:=
repeat match goal with
  | |- armc ⊆ armc => reflexivity
  | |- hastyp_exp armc (ShiftReg _ _ _ _) _ => eapply hastyp_ShiftReg
  | |-hastyp_exp _ (Ones _ _) _ => eapply hastyp_Ones
  | |-hastyp_exp _ (Pack_NZCV _ _ _ _ ) _ => eapply hastyp_Pack_NZCV
  | |-hastyp_exp _ (ConditionHolds _ )_ => eapply hastyp_ConditionHolds
  | |- hastyp_exp armc _ _ => (assumption || estyp)
  | |-context[ SP_read] => unfold SP_read
  | |- arm8typctx R_SP = Some (sizeof_c arm8typctx R_SP) => reflexivity
  | |- _ = _ \/ _ = _ => lia
  | |- n.[_,_] < 2 ^ _ => eapply N.lt_le_trans; [eapply xbits_bound |  psimpl; lia]
  | |- _ < 2 ^_ => lia
  | |- armc (arm_varid _)  = Some 64 =>
 rewrite typeof_arm_varid; reflexivity
  | |- Some _ = armc (arm_varid _) =>
 rewrite typeof_arm_varid; reflexivity
  | |- armc (_) = Some (sizeof_c armc _) =>
   unfold sizeof_c; rewrite typeof_arm_varid; lia
  | |- _ <= sizeof_c armc _ =>
   unfold sizeof_c; rewrite typeof_arm_varid; lia
  | |- (arm_varid _) <> (V_TEMP _ ) =>
  eapply armvarid_neq_temp
  | |- _ <= (if ?c then _ else _) => destruct c; lia
  end.

Local Lemma hastyp_arm_log_imm2il:
  forall op Rn Rd immr imms sf n_ q,
   (n_ < 2)->(sf = 1\/ sf =0)->(imms < 2^6) -> (immr < 2^6)-> (Rn < 2^5) -> (Rd < 2 ^ 5) ->
   arm_log_imm2il op Rn Rd immr imms sf n_ = Some q ->
    hastyp_stmt armc armc q armc.
Proof.
Admitted.

Local Lemma hastyp_arm_mov_imm:
  forall op Rd imm16 size shift,
  (shift < 2 ^ 64)-> (imm16 < 2 ^ 16)-> (size < 2 ^ 64)->
    hastyp_stmt armc armc (arm_mov_imm2il op Rd imm16 size shift) armc.
Proof.
  intros. unfold_stmt.
  destruct op eqn:?;unfold_stmt.
  estyp.
  all: try estyp.  try (assumption||lia).
  all: try unfold widthof_binop; try reflexivity.
  all: try match_awcs; try unfold sizeof_c.
  admit.
  all: try rewrite update_cancel in *; try rewrite update_frame in *.
  all: try assumption.
Admitted.

Local Lemma hastyp_arm_datashft_reg2il:
  forall op sf s shift Rm Rd imm6 Rn,
  (sf = 1\/ sf =0)-> (imm6 < 2 ^ 6) ->
    hastyp_stmt armc armc (arm_datashft_reg2il op 0 sf s shift Rm Rd imm6 Rn) armc.
Proof.
  intros. unfold_stmt.
  destruct op eqn:?;destruct H; subst; unfold_stmt; psimpl.
  all: destruct (shift =? 3) eqn:?.
  all: destruct (N.testbit imm6 5) eqn:Hbit.
  all: try eapply TNop; try reflexivity.
  all: destruct_match_rmr; awc_sub_branch e.
  all: match_awcs.
Admitted.

Local Lemma hastyp_arm_logshft_reg2il:
forall op sf shift Rm Rd imm6 Rn,
(sf = 1\/ sf =0)-> (imm6 < 2 ^ 6) ->
hastyp_stmt armc armc (arm_logshft_reg2il op 0 sf 0 shift Rm Rd imm6 Rn) armc.
Proof.
  intros. unfold_stmt.
  destruct op eqn:?;destruct H; subst; unfold_stmt; psimpl.
  all: destruct (N.testbit imm6 5) eqn:Hbit.
  all: try eapply TNop; try reflexivity.
  all: try eapply hastyp_arm_data_il; try reflexivity.
  all: try estyp.
  all: match_awcs.
Admitted.

Local Lemma hastyp_ExtendReg2:
forall imm3 Rm option_ datasize,
(datasize=32) \/ (datasize=64) ->
hastyp_exp armc
(ExtendReg2 Rm (DecodeRegExtend option_) imm3 datasize) datasize.
Proof.
  intros. unfold ExtendReg2. destruct_match_rmr.
  eapply TUnknown.
  destruct H. subst. discriminate e.
   subst. discriminate e.
Qed.

Local Lemma hastyp_arm_extend_reg2il:
forall op sf s Rm option_ imm3 Rn Rd,
(sf = 1\/ sf =0)-> (imm3 < 2 ^ 3) ->
hastyp_stmt armc armc (arm_extend_reg2il op 0 sf s Rm option_ imm3 Rn Rd) armc.
Proof.
  intros. unfold_stmt.
  destruct op eqn:?;destruct H; subst; unfold_stmt; psimpl.
  all: destruct (4 <? imm3) eqn:Hbit.
  all: try eapply TExn; try reflexivity.
  all: destruct (Rn =?31) eqn: Hbit2.
  all: destruct_match_rmr; awc_sub_branch e.
  all: match_awcs.
Admitted.

Local Lemma hastyp_arm_withcarry_2il:
forall op sf Rm Rn Rd,
(sf = 1\/ sf =0)->
hastyp_stmt armc armc (arm_withcarry_2il op sf Rm Rn Rd) armc.
Proof.
  intros. unfold_stmt.
  destruct op eqn:?;destruct H; subst; unfold_stmt; psimpl.
  all: destruct_match_rmr; awc_sub_branch e.
  all: match_awcs.
Admitted.

Local Lemma hastyp_arm_data_r_shift_il:
forall sf Rm op2 Rn Rd,
(sf = 1\/ sf =0)->
hastyp_stmt armc armc (arm_data_r_shift_il sf Rm op2 Rn Rd true false) armc.
Proof.
  intros. unfold_stmt.
  destruct H; subst; psimpl.
  all: destruct_match_rmr;
  eapply hastyp_arm_data_il.
  all: try reflexivity.
  all: try eapply TUnknown.
  - unfold ShiftReg; unfold ShiftC; destruct_match; estyp.
Admitted.


Local Lemma hastyp_arm_data_i_with_cond:
forall sf Rn imm nzcv cond,
(sf = 1\/ sf =0)->
(cond = 1\/ cond =0)->
(nzcv < 2 ^ 4) ->
(imm < 2 ^ 5) ->
hastyp_stmt armc armc (arm_data_i_with_cond (ARM_CCMN_IMM sf Rn imm nzcv cond) sf Rn imm nzcv cond) armc.
Proof.
  intros. unfold_stmt.
  destruct H; subst.
  all: destruct H0; subst; psimpl.
  all: destruct_match_rmr; awc_sub_branch e.
  all: match_awcs.
Admitted.



  (*final arm2il-C6.2.5*)
  Definition arm2il (a:addr) inst:=
  let il := match inst with
  (*DP imm*)
  | ARM_DATA_IMM op sf s sh imm12 Rn Rd => arm_data_imm2il op sf s sh imm12 Rn Rd
  (*logical imm*)
  | ARM_LOGICAL_IMM op Rn Rd immr imms sf n_ => Nop
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
  | ARM_EXCLUSIVE ARM_CAS size Xn Xs Xt Xt2 => arm_cas2il size Xn Xs Xt
  (*LDAPR/STLR unscaled immediate*)
  | ARM_LOAD_GEN ARM_STLURB Xn Xt imm9 size => arm_stlurb2il Xn Xt imm9
  | ARM_LOAD_GEN ARM_LDAPURB Xn Xt imm9 size => arm_ldapurb2il Xn Xt imm9
  | ARM_LOAD_GEN ARM_LDAPURSB Xn Xt imm9 size => arm_ldapursb2il size Xn Xt imm9
  | ARM_LOAD_GEN ARM_STLURH Xn Xt imm9 size => arm_stlurh2il Xn Xt imm9
  | ARM_LOAD_GEN ARM_LDAPURH Xn Xt imm9 size => arm_ldapurh2il Xn Xt imm9
  | ARM_LOAD_GEN ARM_LDAPURSH Xn Xt imm9 size => arm_ldapursh2il size Xn Xt imm9
  | ARM_LOAD_GEN ARM_LDAPUR Xn Xt imm9 size => arm_ldapur2il Xn Xt imm9 size
  | ARM_LOAD_GEN ARM_LDAPURSW Xn Xt imm9 size => arm_ldapursw2il size Xn Xt imm9
  | ARM_LOAD_GEN ARM_STLUR Xn Xt imm9 size => arm_stlur2il size Xn Xt imm9
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
  | ARM_LD_REG_LIT ARM_LDR_LIT Xt imm19 size => arm_ldr_lit2il size Xt imm19
  | ARM_LD_REG_LIT ARM_LDRSW_LIT Xt imm19 size => arm_ldrsw_lit2il Xt imm19
  | ARM_LD_REG_LIT ARM_PRFM_LIT Xt imm19 size => arm_prfm_lit2il Xt imm19
  (*load/store no-allocate pair (offset)*)
  | ARM_STNP Xn Xt Xt2 imm7 scale => arm_stnp2il Xn Xt Xt2 imm7 scale
  | ARM_LDNP Xn Xt Xt2 imm7 scale => arm_ldnp2il Xn Xt Xt2 imm7 scale
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
  | ARM_INDEXED ARM_LDRSB_IMM Xn Xt imm912 size signed wback postindex => arm_ldrsb_imm2il size Xn Xt imm912 signed wback postindex
  | ARM_INDEXED ARM_LDR_IMM Xn Xt imm912 size signed wback postindex => arm_ldr_imm2il Xn Xt imm912 size signed wback postindex
  | ARM_INDEXED ARM_STRH_IMM Xn Xt imm912 size signed wback postindex => arm_strh_imm2il Xn Xt imm912 signed wback postindex
  | ARM_INDEXED ARM_LDRH_IMM Xn Xt imm912 size signed wback postindex => arm_ldrh_imm2il Xn Xt imm912 signed wback postindex
  | ARM_INDEXED ARM_LDRSH_IMM Xn Xt imm912 size signed wback postindex => arm_ldrsh_imm2il size Xn Xt imm912 signed wback postindex
  | ARM_INDEXED ARM_STR_IMM Xn Xt imm912 size signed wback postindex => arm_str_imm2il size Xn Xt imm912 signed wback postindex
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
  | ARM_LD_STR_REG ARM_LDRSB_REG Xn Xm Xt extend size _=> arm_ldrsb_reg2il size 0 Xn Xm Xt extend
  | ARM_LD_STR_REG ARM_STRH_REG Xn Xm Xt extend _ s => arm_strh_reg2il Xn Xm Xt extend
  | ARM_LD_STR_REG ARM_LDRH_REG Xn Xm Xt extend _ s => arm_ldrh_reg2il Xn Xm Xt extend
  | ARM_LD_STR_REG ARM_LDRSH_REG Xn Xm Xt extend size s => arm_ldrsh_reg2il size Xn Xm Xt extend s
  | ARM_LD_STR_REG ARM_STR_REG Xn Xm Xt extend size s => arm_str_reg2il size s Xn Xm Xt extend
  | ARM_LD_STR_REG ARM_LDR_REG Xn Xm Xt extend size s => arm_ldr_reg2il size s Xn Xm Xt extend
  | ARM_LD_STR_REG ARM_LDRSW_REG Xn Xm Xt extend _ s => arm_ldrsw_reg2il Xn Xm Xt extend s
(* | ARM_LD_STR_REG ARM_PRFM_REG Xn Xm Xt extend _ s => havoc) *)
  | UDF => Exn 4
  |_ => havoc end in
  (*Seq (Move R_PC (Word (a+8 mod 2^64) 64))*) il.


Lemma hastyp_awc_in_arm_data_il:
forall datasize x y carry_in assign assign_flags Rn,
  datasize = 64 \/ datasize = 32->
  hastyp_exp arm8typctx x datasize ->
  hastyp_exp arm8typctx y datasize ->
  hastyp_exp arm8typctx carry_in 1 ->
  hastyp_stmt armc armc
(let '(result, nzcv) := AddWithCarry datasize x y carry_in in
arm_data_il assign assign_flags Rn result nzcv) arm8typctx.
Proof.
  intros.
  eapply hastyp_arm_data_il with (datasize := datasize). reflexivity. assumption.
  - eapply TBinOp with (bop:= OP_PLUS). estyp. assumption. assumption.
  eapply TCast with (w:= 1). assumption. lia.
  -  eapply hastyp_Pack_NZCV.
  all: etyp; try (eassumption || lia || eapply ones_bound).
  Qed.

  Lemma hastyp_awc_in_arm_data_il_cond:
forall datasize x y carry_in assign assign_flags Rn n0 m,
  datasize = 64 \/ datasize = 32->
  (n0 < 2 ^ 4)-> (m < 2 ^ 4)->
  hastyp_exp arm8typctx x datasize ->
  hastyp_exp arm8typctx y datasize ->
  hastyp_exp arm8typctx carry_in 1 ->
  hastyp_stmt armc armc
(let '(result, nzcv) := AddWithCarry datasize x y carry_in in
arm_data_il assign assign_flags Rn result (Ite (ConditionHolds m) nzcv (Word n0 4))) arm8typctx.
Proof.
  intros.
  eapply hastyp_arm_data_il with (datasize := datasize). reflexivity. assumption.
  - eapply TBinOp with (bop:= OP_PLUS). estyp. assumption. assumption.
  eapply TCast with (w:= 1). assumption. lia.
  - estyp. eapply hastyp_ConditionHolds. reflexivity. assumption. eapply hastyp_Pack_NZCV.
  all: try etyp;try (eassumption || lia || eapply ones_bound).
  Admitted.

Theorem welltyped_arm82il:
  forall a n imm imm16 size shift imm12 nzcv,
  (a + 8 mod 2 ^ 64 < 2 ^ (sizeof_c arm8typctx R_PC))->
  (imm < 2 ^ 64)-> (imm16 < 2 ^ 16) ->
  (imm12 < 2 ^ 12) ->(size < 2 ^ 64)
  -> (shift < 2^64) ->(nzcv < 2 ^ 4) ->
  hastyp_stmt arm8typctx arm8typctx (arm2il a (arm_decode n)) arm8typctx.
Proof.
  intros.
    unfold arm_decode, dp_imm, branch_exc, load_store, dp_reg, dp_fp_simd.
  unfold
    data_proc_3_src, cond_select, cond_compare_imm, cond_compare_reg, evaluate,
    rotate, add_sub_carry, add_sub_extended, add_sub_shifted, data_proc_logical,
    data_proc_1_src, data_proc_2_src, ldapr_stlr_imm_u, load_store_exclusive, load_store_mem_tags,
    test_and_b, comp_and_b, uncond_b_imm, uncond_b_reg, sys_reg_move,
    sys_inst, pstate, barriers, hints, exc_gen,
    cond_branch, extract, bitfield, move_wide_imm, logical_imm,
    add_sub_imm, pc_rel,
    load_reg_literal, load_store_no_alloc_pair, load_store_post_indx_pair,
    load_store_pair_offset, load_store_pre_indx_pair, load_store_reg_imm_u,
    load_store_reg_imm_poi, load_store_reg_unpriv, atomic, load_store_reg_off,
    load_store_reg_pac, load_store_reg_u_imm, load_store_reg_imm_pre,arm_data_r_extended.
    destruct_match.
    all: try repeat unfold_stmt.  (*935*)
    all: try eapply TNop; try reflexivity. (*921*)
    all: try eapply TExn; try reflexivity.
    all: try unfold SP_read. (*428*)
    all: try match goal with
    | |- context[ConditionHolds] =>
    do 2 try match goal with [ |- context [if ?c then _ else _] ] => destruct c end;
     eapply hastyp_awc_in_arm_data_il_cond;
     try repeat first [eapply N.lt_le_trans; [eapply xbits_bound |  psimpl; lia]
    | unfold sizeof_c; rewrite typeof_arm_varid | lia | estyp]
    | |- context[AddWithCarry] =>
    repeat try match goal with [ |- context [if ?c then _ else _] ] => destruct c end;
     try eapply hastyp_awc_in_arm_data_il;
     try destruct_match;
     try repeat first [eapply N.lt_le_trans; [eapply xbits_bound |  psimpl; lia]
    | unfold sizeof_c; rewrite typeof_arm_varid | lia | estyp]
    end. (*412*)
Admitted.