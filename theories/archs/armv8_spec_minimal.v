(* Decoder/lifter for Armv8-A A64, based on the Arm ARM issue E.a (DDI0487E.a).
   Cleaned-up copy of armv8_lifter_rework.v, laid out like armv7_lifter.v:
     instruction syntax -> decoding -> lifting -> program.
   "FIX Dn/Sn" marks a place that deviates from armv8_lifter_rework.v to match the
   manual; the full list is at the bottom of this file.
   Well-typedness: welltyped_arm8_prog (end of file) proves every lifted instruction is well typed. *)

From Picinae.archs Require Import armv8 armv8_PIL_notation.
Import armv8_PIL_notation.Notation.
From Stdlib Require Import List String Ascii NArith ZArith Bool Lia.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope N_scope.

(* Bit-pattern matching:  match[bits] x, y with | "01x  !=11" => a | ... else d end
   Cases are tried in order; "x" is a don't-care bit, "-" matches anything,
   "!=" negates a pattern. *)
Module BitPatterns.
  Definition shift_add n (b: bool) :=
    match n with
    | N0 => if b then Npos xH else N0
    | Npos p => if b then Npos (xI p) else Npos (xO p)
    end.
  Definition parse_pattern pat :=
    let (s, e) := match pat with String "!" (String "=" s') => (s', false) | _ => (pat, true) end in
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
    (fix F s1 s2 := match s1 with EmptyString => s2 | String c s' => F s' (String c s2) end) s "".
  Fixpoint split_str s curr :=
    match s with
    | EmptyString => match curr with EmptyString => [] | _ => [rev_str curr] end
    | String c s' =>
        match c, curr with
        | " ", EmptyString => split_str s' ""%string
        | " ", _           => rev_str curr :: split_str s' ""%string
        | _  , _           => split_str s' (String c curr)
        end%char
    end.
  Definition match_pattern n pat :=
    let '(val, mask, e) := parse_pattern pat in
    if e then (N.land n mask =? val) else negb (N.land n mask =? val).
  Fixpoint match_all_patterns ns pats :=
    match ns, pats with
    | [n], [pat] => match_pattern n pat
    | n::ns', pat::pats' => match_pattern n pat && match_all_patterns ns' pats'
    | _, _ => false
    end.
  Fixpoint select_pattern_list {A} (ns: list N) (default: A) (cases: list (string * A)) : A :=
    match cases with
    | nil => default
    | (pats, act)::cases' =>
        if match_all_patterns ns (split_str pats "") then act else select_pattern_list ns default cases'
    end.
  Notation "pats => val" := (pats, val) (at level 201, only parsing).
  Notation "'match[bits]' n0 , .. , nn 'with' | c0 | .. | cn 'else' d 'end'" := (
     match n0::..[nn].., c0::..[cn].. with ns, cases =>
       ltac:(let r := eval cbn in (select_pattern_list ns d cases) in exact r)
     end) (at level 0, c0 at level 201, only parsing).
  Notation "n .[ i , j ]" := (xbits n i j) (at level 30, format "n .[ i , j ]").
  Notation "n .[ b ]" := (xbits n b (N.succ b)) (at level 30, format "n .[ b ]").
End BitPatterns.
Import BitPatterns.

Definition ds sf := if sf =? 0 then 32 else 64. (* datasize *)


(********** instruction syntax **********)

Variant arm_atomic_op := AT_ADD | AT_CLR | AT_EOR | AT_SET | AT_SMAX | AT_SMIN | AT_UMAX | AT_UMIN | AT_SWP.

Variant arm_inst :=
  | ARM_UNDEFINED (* unallocated or UNDEFINED encoding *)
  | idk           (* valid, but not modelled (system, CRC32, FP/SIMD, ...) *)
  | ARM_NOP       (* hints, barriers, prefetches *)

  (* data processing - immediate: C4.1.2 *)
  | ARM_ADR (op immlo immhi Rd: N)                 (* op=1: ADRP *)
  | ARM_addsub_i (sf op S sh imm12 Rn Rd: N)
  | ARM_logic_i (sf opc N_ immr imms Rn Rd: N)
  | ARM_movw (sf opc hw imm16 Rd: N)               (* MOVN, MOVZ, MOVK *)
  | ARM_bfm (sf opc N_ immr imms Rn Rd: N)         (* SBFM, BFM, UBFM *)
  | ARM_EXTR (sf Rm lsb Rn Rd: N)

  (* branches, exception generating and system: C4.1.3 *)
  | ARM_B_cond (cond imm19: N)
  | ARM_B (op imm26: N)                            (* op=1: BL *)
  | ARM_br (opc Rn: N)                             (* BR, BLR, RET *)
  | ARM_CBZ (sf op imm19 Rt: N)                    (* op=1: CBNZ *)
  | ARM_TBZ (b5 op b40 imm14 Rt: N)                (* op=1: TBNZ *)
  | ARM_pstate (op1 op2: N)                        (* CFINV, XAFLAG, AXFLAG, MSR (immediate) *)
  | ARM_SYSL (Rt: N)                               (* SYSL: result is UNKNOWN (implementation defined) *)

  (* loads and stores: C4.1.4 *)
  | ARM_ls (size opc Rn Rt off: N) (wback post: bool) (* single register, immediate offset *)
  | ARM_ls_r (size opc Rn Rt Rm option S: N)          (* single register, register offset *)
  | ARM_ldr_lit (opc imm19 Rt: N)
  | ARM_lsp (opc L Rn Rt Rt2 imm7: N) (wback post: bool) (* register pairs *)
  | ARM_stx (size: N) (pair: bool) (Rs Rn Rt Rt2: N)  (* store exclusive *)
  | ARM_cas (sz: N) (pair: bool) (Rs Rn Rt: N)        (* compare and swap *)
  | ARM_atomic (op: arm_atomic_op) (size Rs Rn Rt: N)
  | ARM_tag (opc imm9 op2 Rn Rt: N)                   (* STG, STZG, ST2G, STZ2G, LDG *)

  (* data processing - register: C4.1.5 *)
  | ARM_logic_r (sf opc shift N_ Rm imm6 Rn Rd: N)
  | ARM_addsub_r (sf op S shift Rm imm6 Rn Rd: N)
  | ARM_addsub_x (sf op S Rm option imm3 Rn Rd: N)
  | ARM_adc (sf op S Rm Rn Rd: N)                  (* ADC, ADCS, SBC, SBCS *)
  | ARM_ccmp (sf op Rm cond imm nzcv Rn: N)        (* CCMN, CCMP; imm=1: Rm is imm5 *)
  | ARM_csel (sf op Rm cond o2 Rn Rd: N)           (* CSEL, CSINC, CSINV, CSNEG *)
  | ARM_dp1 (sf opc Rn Rd: N)                      (* RBIT, REV16, REV32, REV, CLZ, CLS *)
  | ARM_dp2 (sf opc Rm Rn Rd: N)                   (* UDIV, SDIV, LSLV, LSRV, ASRV, RORV *)
  | ARM_dp3 (sf op31 Rm o0 Ra Rn Rd: N).           (* MADD, MSUB, [SU]MADDL, [SU]MSUBL, [SU]MULH *)


(********** decoding **********)

Section Decoder.
Variable n : N.
Let sf := n.[31].
Let Rd := n.[0,5].
Let Rt := n.[0,5].
Let Rn := n.[5,10].
Let Rt2 := n.[10,15].
Let Rm := n.[16,21].
Let size := n.[30,32].

(* C4.1.2 *)
Definition dp_imm :=
  let opc := n.[29,31] in let N_ := n.[22] in let immr := n.[16,22] in let imms := n.[10,16] in
  match n.[23,26] with
  | 0 | 1 => ARM_ADR (n.[31]) (n.[29,31]) (n.[5,24]) Rd
  | 2 => ARM_addsub_i sf (n.[30]) (n.[29]) (n.[22]) (n.[10,22]) Rn Rd
  | 3 => idk (* ADDG, SUBG *)
  | 4 => if sf <? N_ then ARM_UNDEFINED else ARM_logic_i sf opc N_ immr imms Rn Rd
  | 5 => if (opc =? 1) || (sf <? n.[22]) then ARM_UNDEFINED else ARM_movw sf opc (n.[21,23]) (n.[5,21]) Rd
  | 6 => if (opc =? 3) || negb (sf =? N_) || (sf =? 0) && ((32 <=? immr) || (32 <=? imms))
         then ARM_UNDEFINED else ARM_bfm sf opc N_ immr imms Rn Rd
  | _ => if (opc =? 0) && (n.[21] =? 0) && (sf =? N_) && (imms <? ds sf)
         then ARM_EXTR sf Rm imms Rn Rd else ARM_UNDEFINED
  end.

(* C4.1.3 *)
Definition exc_gen :=
  if negb (n.[2,5] =? 0) then ARM_UNDEFINED else
  match n.[21,24], n.[0,2] with
  | (0 | 5), (1 | 2 | 3) => idk (* SVC, HVC, SMC, DCPS1-3 *)
  | (1 | 2), 0 => idk           (* BRK, HLT *)
  | _, _ => ARM_UNDEFINED
  end.

Definition barriers := (* CLREX, DSB, SSBB, PSSBB, DMB, ISB, SB *)
  let op2 := n.[5,8] in
  if (2 <=? op2) && negb (op2 =? 3) && (Rt =? 31) then ARM_NOP else ARM_UNDEFINED.

Definition uncond_b_reg :=
  let opc := n.[21,25] in let op3 := n.[10,16] in let op4 := n.[0,5] in
  if negb (n.[16,21] =? 31) then ARM_UNDEFINED
  else if (opc <=? 2) && (op3 =? 0) && (op4 =? 0) then ARM_br opc Rn
  else if (op3 =? 0) && (Rn =? 31) && (op4 =? 0) && ((opc =? 4) || (opc =? 5)) then idk (* ERET, DRPS *)
  else ARM_UNDEFINED. (* incl. BRAA*, BLRAA*, RETAA*, ERETAA*: FEAT_PAuth not implemented *)

Definition branch_sys :=
  match[bits] n.[29,32], n.[12,26], n.[0,5] with
  | "010  0xxxxxxxxxxxxx  -    " => if (n.[24] =? 0) && (n.[4] =? 0) then ARM_B_cond (n.[0,4]) (n.[5,24]) else ARM_UNDEFINED
  | "110  00xxxxxxxxxxxx  -    " => exc_gen
  | "110  01000000110010  11111" => ARM_NOP (* FIX D1: hints (incl. PAC/BTI hints) execute as NOP *)
  | "110  01000000110011  -    " => barriers
  | "110  0100000xxx0100  -    " => if Rt =? 31 then ARM_pstate (n.[16,19]) (n.[5,8]) else ARM_UNDEFINED (* FIX D2 *)
  | "110  0100x01xxxxxxx  -    " => if n.[21] =? 1 then ARM_SYSL Rt else idk (* SYSL, SYS *)
  | "110  0100x1xxxxxxxx  -    " => idk (* MSR (register), MRS *)
  | "110  1xxxxxxxxxxxxx  -    " => uncond_b_reg
  | "x00  -               -    " => ARM_B (n.[31]) (n.[0,26])
  | "x01  0xxxxxxxxxxxxx  -    " => ARM_CBZ sf (n.[24]) (n.[5,24]) Rt
  | "x01  1xxxxxxxxxxxxx  -    " => ARM_TBZ (n.[31]) (n.[24]) (n.[19,24]) (n.[5,19]) Rt
  else ARM_UNDEFINED end.

(* C4.1.4 *)
Definition ls_simd form := (* V=1 *)
  if (form =? 2) || (2 <=? n.[22,24]) && (0 <? size) then ARM_UNDEFINED else idk.

(* form = op4: unscaled (0), post-index (1), unprivileged (2), pre-index (3).  LDAPR/STLR
   (unscaled immediate) decode like the unprivileged form. *)
Definition ls_imm form :=
  let opc := n.[22,24] in
  if n.[26] =? 1 then ls_simd form
  else if (opc =? 3) && (2 <=? size) || (size =? 3) && (opc =? 2) && negb (form =? 0) then ARM_UNDEFINED
  else ARM_ls size opc Rn Rt (scast 9 64 (n.[12,21])) (N.odd form) (form =? 1). (* FIX D3 *)

Definition ls_uimm :=
  let opc := n.[22,24] in
  if n.[26] =? 1 then ls_simd 0
  else if (opc =? 3) && (2 <=? size) then ARM_UNDEFINED
  else ARM_ls size opc Rn Rt (N.shiftl (n.[10,22]) size) false false. (* FIX D4 *)

Definition ls_reg :=
  let opc := n.[22,24] in
  if n.[14] =? 0 then ARM_UNDEFINED
  else if n.[26] =? 1 then ls_simd 0
  else if (opc =? 3) && (2 <=? size) then ARM_UNDEFINED
  else ARM_ls_r size opc Rn Rt Rm (n.[13,16]) (n.[12]).

Definition ldr_lit :=
  let opc := n.[30,32] in
  if opc =? 3 then (if n.[26] =? 0 then ARM_NOP (* PRFM *) else ARM_UNDEFINED)
  else if n.[26] =? 1 then idk else ARM_ldr_lit opc (n.[5,24]) Rt.

Definition ldst_pair := (* op2: no-allocate (0), post-index (1), offset (2), pre-index (3) *)
  let opc := n.[30,32] in let op2 := n.[23,25] in
  if opc =? 3 then ARM_UNDEFINED
  else if n.[26] =? 1 then idk
  else if (op2 =? 0) && (opc =? 1) then ARM_UNDEFINED
  else ARM_lsp opc (n.[22]) Rn Rt Rt2 (n.[15,22]) (N.odd op2) (op2 =? 1).

Definition ldst_excl :=
  let o2 := n.[23] in let L := n.[22] in let Rs := n.[16,21] in
  if n.[21] =? 0 then
    if o2 =? 1 then ARM_ls size L Rn Rt 0 false false        (* STLLR, STLR, LDLAR, LDAR *)
    else if L =? 1 then ARM_ls size 1 Rn Rt 0 false false    (* LDXR, LDAXR *)
    else ARM_stx size false Rs Rn Rt Rt2                     (* STXR, STLXR *)
  else if (o2 =? 1) || (size <? 2) then
    if negb (Rt2 =? 31) then ARM_UNDEFINED
    else if o2 =? 1 then ARM_cas size false Rs Rn Rt         (* CAS *)
    else ARM_cas (2 + size) true Rs Rn Rt                    (* CASP *)
  else if L =? 1 then ARM_lsp (2 * (size - 2)) 1 Rn Rt Rt2 0 false false (* LDXP, LDAXP: FIX D9 *)
  else ARM_stx size true Rs Rn Rt Rt2.                       (* STXP, STLXP: FIX D5 *)

Definition atomic :=
  let opc := n.[12,15] in
  if n.[26] =? 1 then ARM_UNDEFINED
  else if n.[15] =? 0 then
    ARM_atomic (match opc with 0 => AT_ADD | 1 => AT_CLR | 2 => AT_EOR | 3 => AT_SET
                | 4 => AT_SMAX | 5 => AT_SMIN | 6 => AT_UMAX | _ => AT_UMIN end) size (n.[16,21]) Rn Rt
  else if opc =? 0 then ARM_atomic AT_SWP size (n.[16,21]) Rn Rt
  else if (opc =? 4) && (n.[23] =? 1) && (n.[22] =? 0) then ARM_ls size 1 Rn Rt 0 false false (* LDAPR *)
  else ARM_UNDEFINED.

Definition ldst_tags :=
  let opc := n.[22,24] in let imm9 := n.[12,21] in let op2 := n.[10,12] in
  if negb (op2 =? 0) || (opc =? 1) then ARM_tag opc imm9 op2 Rn Rt
  else if imm9 =? 0 then idk (* STZGM, STGM, LDGM *) else ARM_UNDEFINED.

Definition load_store :=
  match[bits] n.[28,32], n.[26], n.[23,25], n.[16,22], n.[10,12] with
  | "0x00  1  00  000000  - " => idk (* SIMD load/store multiple structures *)
  | "0x00  1  01  0xxxxx  - " => idk
  | "0x00  1  0x  1xxxxx  - " => ARM_UNDEFINED
  | "0x00  1  10  x00000  - " => idk (* SIMD load/store single structure *)
  | "0x00  1  11  -       - " => idk
  | "0x00  1  x0  -       - " => ARM_UNDEFINED
  | "1101  0  1x  1xxxxx  - " => ldst_tags
  | "1x00  1  -   -       - " => ARM_UNDEFINED
  | "xx00  0  0x  -       - " => ldst_excl
  | "xx01  0  1x  0xxxxx  00" => ls_imm 2 (* LDAPR/STLR (unscaled immediate) *)
  | "xx01  -  0x  -       - " => ldr_lit
  | "xx10  -  -   -       - " => ldst_pair
  | "xx11  -  0x  0xxxxx  - " => ls_imm (n.[10,12])
  | "xx11  -  0x  1xxxxx  00" => atomic
  | "xx11  -  0x  1xxxxx  10" => ls_reg
  | "xx11  -  0x  1xxxxx  x1" => ARM_UNDEFINED (* LDRAA, LDRAB: FEAT_PAuth not implemented *)
  | "xx11  -  1x  -       - " => ls_uimm
  else ARM_UNDEFINED end.

(* C4.1.5 *)
Definition dp2 :=
  let op := n.[10,16] in
  if n.[29] =? 1 then (if (sf =? 1) && (op =? 0) then idk (* SUBPS *) else ARM_UNDEFINED)
  else if (op =? 2) || (op =? 3) || (8 <=? op) && (op <=? 11) then ARM_dp2 sf op Rm Rn Rd (* FIX D8 *)
  else if (sf =? 1) && ((op =? 0) || (op =? 4) || (op =? 5))  (* SUBP, IRG, GMI; PACGA is UNDEFINED (no FEAT_PAuth) *)
       || (16 <=? op) && (op <=? 23) && (op mod 4 <? 3 + sf) && (3 * sf <=? op mod 4) (* CRC32[C] *)
  then idk else ARM_UNDEFINED.

Definition dp1 :=
  let op2 := n.[16,21] in let op := n.[10,16] in
  if n.[29] =? 1 then ARM_UNDEFINED
  else if op2 =? 0 then (if (5 <? op) || (sf =? 0) && (op =? 3) then ARM_UNDEFINED else ARM_dp1 sf op Rn Rd)
  else ARM_UNDEFINED. (* incl. PAC*, AUT*, XPAC*: FEAT_PAuth not implemented *)

Definition dp3 :=
  let op31 := n.[21,24] in let o0 := n.[15] in
  if (n.[29,31] =? 0) && ((op31 =? 0) || (sf =? 1) && ((op31 =? 1) || (op31 =? 5) || ((op31 =? 2) || (op31 =? 6)) && (o0 =? 0)))
  then ARM_dp3 sf op31 Rm o0 (n.[10,15]) Rn Rd else ARM_UNDEFINED.

Definition dp_reg :=
  match[bits] n.[30], n.[28], n.[21,25], n.[10,16] with
  | "0  1  0110  -     " => dp2
  | "1  1  0110  -     " => dp1
  | "-  0  0xxx  -     " => if sf <? n.[15] then ARM_UNDEFINED else ARM_logic_r sf (n.[29,31]) (n.[22,24]) (n.[21]) Rm (n.[10,16]) Rn Rd
  | "-  0  1xx0  -     " => if (n.[22,24] =? 3) || (sf <? n.[15]) then ARM_UNDEFINED else ARM_addsub_r sf (n.[30]) (n.[29]) (n.[22,24]) Rm (n.[10,16]) Rn Rd
  | "-  0  1xx1  -     " => if negb (n.[22,24] =? 0) || (4 <? n.[10,13]) then ARM_UNDEFINED else ARM_addsub_x sf (n.[30]) (n.[29]) Rm (n.[13,16]) (n.[10,13]) Rn Rd
  | "-  1  0000  000000" => ARM_adc sf (n.[30]) (n.[29]) Rm Rn Rd
  | "-  1  0000  x00001" => if (sf =? 1) && (n.[29,31] =? 1) && (n.[4] =? 0) then idk (* RMIF *) else ARM_UNDEFINED
  | "-  1  0000  xx0010" => if (sf =? 0) && (n.[29,31] =? 1) && (n.[15,21] =? 0) && (n.[0,5] =? 13) then idk (* SETF8/16 *) else ARM_UNDEFINED
  | "-  1  0010  -     " => if (n.[29] =? 1) && (n.[10] =? 0) && (n.[4] =? 0) then ARM_ccmp sf (n.[30]) Rm (n.[12,16]) (n.[11]) (n.[0,4]) Rn else ARM_UNDEFINED
  | "-  1  0100  -     " => if (n.[29] =? 0) && (n.[11] =? 0) then ARM_csel sf (n.[30]) Rm (n.[12,16]) (n.[10]) Rn Rd else ARM_UNDEFINED
  | "-  1  1xxx  -     " => dp3
  else ARM_UNDEFINED end.

(* C4.1 *)
Definition arm_decode :=
  match[bits] n.[25,29] with
  | "100x" => dp_imm
  | "101x" => branch_sys
  | "x1x0" => load_store
  | "x101" => dp_reg
  | "x111" => idk (* FP/SIMD *)
  else ARM_UNDEFINED end.

End Decoder.


(********** lifting **********)

Notation "'PC'" := (Var R_PC) (in custom PIL at level 0).
Notation "'N'" := (Var R_NG) (in custom PIL at level 0).
Notation "'Z'" := (Var R_ZR) (in custom PIL at level 0).
Notation "'C'" := (Var R_CY) (in custom PIL at level 0).
Notation "'V'" := (Var R_OV) (in custom PIL at level 0).
Notation tmp := (V_TEMP 1).
Notation T := (Var tmp).

Definition UNDEF := Exn 4. (* FIX S1 *)
Definition havoc := Exn 0. (* not modelled *)

(* CONSTRAINED UNPREDICTABLE: UNDEFINED, NOP, or one of the permitted alternatives. *)
Definition CU (alts: list stmt) := fold_right (fun q r => If (Unknown 1) q r) Nop (UNDEF :: alts).

Definition arm_varid n :=
  match n with
  | 0 => R_X0 | 1 => R_X1 | 2 => R_X2 | 3 => R_X3 | 4 => R_X4 | 5 => R_X5 | 6 => R_X6 | 7 => R_X7
  | 8 => R_X8 | 9 => R_X9 | 10 => R_X10 | 11 => R_X11 | 12 => R_X12 | 13 => R_X13 | 14 => R_X14
  | 15 => R_X15 | 16 => R_X16 | 17 => R_X17 | 18 => R_X18 | 19 => R_X19 | 20 => R_X20 | 21 => R_X21
  | 22 => R_X22 | 23 => R_X23 | 24 => R_X24 | 25 => R_X25 | 26 => R_X26 | 27 => R_X27 | 28 => R_X28
  | 29 => R_X29 | 30 => R_X30 | _ => R_XZR
  end.

(* Register access (FIX S2, S3): xr/wx treat register 31 as ZR, sr/ws treat it as SP.
   Reads return the low w bits; writes zero-extend a w-bit value to 64 bits. *)
Definition low w e := if w =? 64 then e else Cast CAST_LOW w e.
Definition zx64 w e := if w =? 64 then e else Cast CAST_UNSIGNED 64 e.
Definition xr w n := if n =? 31 then Word 0 w else low w (Var (arm_varid n)).
Definition sr w n := low w (Var (if n =? 31 then R_SP else arm_varid n)).
Definition wx w n e := if n =? 31 then Nop else Move (arm_varid n) (zx64 w e).
Definition ws w n e := Move (if n =? 31 then R_SP else arm_varid n) (zx64 w e).

Definition ld a b := Load (Var V_MEM64) a LittleE b.
Definition st a b e := Move V_MEM64 (Store (Var V_MEM64) a e LittleE b).

(* EL0 SP alignment check (SCTLR_EL1.SA0), done whenever the base register is SP. *)
Definition spchk n :=
  if n =? 31 then <{ if {Var SCTLR_E1}[4] & ({Var R_SP}[3:0] <> 0#4) then exn 0 else nop end }> else Nop.

Definition pcrel imm b := <{ PC + {scast b 64 (N.shiftl imm 2)}#64 }>.

(* J1: ConditionHolds *)
Definition ConditionHolds (cond: N) : exp :=
  let flip := Word (xbits cond 0 1) 1 in
  match xbits cond 1 4 with
  | 0 => <{flip ^ (Z = 1#1)}>
  | 1 => <{flip ^ (C = 1#1)}>
  | 2 => <{flip ^ (N = 1#1)}>
  | 3 => <{flip ^ (V = 1#1)}>
  | 4 => <{flip ^ (C = 1#1 & Z = 0#1)}>
  | 5 => <{flip ^ (N = V)}>
  | 6 => <{flip ^ (N = V & Z = 0#1)}>
  | _ => <{1#1}>
  end.

(* Flags are computed from the result in T before any register is written.
   C is assigned last since its expression may read the old carry. *)
Definition setflags n z c v := <{ R_NG := n; R_ZR := z; R_OV := v; R_CY := c }>.
Definition logic_flags w := setflags <{hcast 1 T}> <{T = 0#w}> <{0#1}> <{0#1}>.

(* J1: AddWithCarry (FIX S6, S7): T := x + y + c; set NZCV if S; then dst T. *)
Definition awc_il w (S: bool) (dst: exp -> stmt) x y c :=
  <{ tmp := x + y + ucast w c;
     {if S then setflags <{hcast 1 T}> <{T = 0#w}> <{(T < x) | (c & (T = x))}> <{hcast 1 ((x ^ T) & (y ^ T))}> else Nop};
     {dst T} }>.
Definition addsub w op S dst x y c := awc_il w S dst x (if op =? 1 then <{!y}> else y) c.

Definition logic_il w opc x y (dst: exp -> stmt) := (* opc: AND, ORR, EOR, ANDS *)
  <{ tmp := {match opc with 1 => <{x | y}> | 2 => <{x ^ y}> | _ => <{x & y}> end};
     {if opc =? 3 then logic_flags w else Nop}; {dst T} }>. (* FIX S11 *)

(* J1: ShiftReg; typ 0 LSL, 1 LSR, 2 ASR, 3 ROR (amt < w) *)
Definition shift_exp w typ x amt :=
  match typ with
  | 0 => <{x << amt}> | 1 => <{x >> amt}> | 2 => <{x >>a amt}>
  | _ => <{(x >> amt) | (x << (w#w - amt))}>
  end.

(* J1: ExtendReg (FIX S9) *)
Definition ext_exp w x opt sh :=
  let len := N.min (N.shiftl 8 (opt mod 4)) (w - sh) in
  <{ {Cast (if opt <? 4 then CAST_UNSIGNED else CAST_SIGNED) w (Extract (len - 1) 0 x)} << sh#w }>.

(* J1: DecodeBitMasks; None when UNDEFINED (FIX S12) *)
Definition ROR e r x := N.lor (N.shiftr x r) (N.shiftl x (e - r)) mod 2^e.
Definition Replicate w e x := N.iter (N.pred (w / e)) (fun acc => cbits acc e x) x mod 2^w.
Definition DecodeBitMasks (immN imms immr: N) (immediate: bool) (M: N) : option (N * N) :=
  let len := N.pred (N.size (cbits immN 6 (N.lnot imms 6))) in
  let levels := N.ones len in
  if (len =? 0) || (M <? N.shiftl 1 len) || immediate && (N.land imms levels =? levels) then None else
  let S := N.land imms levels in let R := N.land immr levels in
  let esize := N.shiftl 1 len in
  let d := xbits (sbop2 Z.sub 6 S R) 0 len in
  Some (Replicate M esize (ROR esize R (N.ones (S + 1))), Replicate M esize (N.ones (d + 1))).

(* Reverse the e-bit elements within each c-bit container of w-bit x (REV*, RBIT). *)
Definition rev_exp w c e x :=
  let sq k := map N.of_nat (seq 0 (N.to_nat k)) in
  let m := c / e in
  match flat_map (fun k => map (fun j => let i := k * m + j in Extract (i * e + e - 1) (i * e) x) (sq m))
                 (rev (sq (w / c))) with
  | [] => x
  | h :: t => fold_left Concat t h
  end.

(* Transfer one 2^size-byte register:  opc 0 store, 1 load, 2 signed load to 64 bits
   (prefetch if size=3), 3 signed load to 32 bits.  unk: the value is UNKNOWN. *)
Definition xfer size opc Rt a (unk: bool) :=
  let b := 2^size in
  let v := if unk then Unknown (8 * b) else ld a b in
  match opc with
  | 0 => st a b (if unk then Unknown (8 * b) else xr (8 * b) Rt)
  | 1 => wx 64 Rt (zx64 (8 * b) v)
  | 2 => if size =? 3 then Nop else wx 64 Rt (Cast CAST_SIGNED 64 v)
  | _ => wx 32 Rt (Cast CAST_SIGNED 32 v)
  end.


(* data processing - immediate *)

Definition adr_il op immlo immhi Rd := (* C6.2.10-11 *)
  let imm := cbits immhi 2 immlo in
  wx 64 Rd (if op =? 0 then <{PC + {scast 21 64 imm}#64}>
            else <{(PC & {N.lnot 4095 64}#64) + {scast 33 64 (N.shiftl imm 12)}#64}>).

Definition logic_i_il sf opc N_ immr imms Rn Rd := (* C6.2: AND, ORR, EOR, ANDS (immediate) *)
  let w := ds sf in
  match DecodeBitMasks N_ imms immr true w with
  | None => UNDEF
  | Some (wm, _) => logic_il w opc (xr w Rn) (Word wm w) (if opc =? 3 then wx w Rd else ws w Rd)
  end.

Definition movw_il sf opc hw imm16 Rd := (* C6.2: MOVN, MOVZ, MOVK *)
  let w := ds sf in let p := 16 * hw in let k := N.shiftl imm16 p mod 2^w in
  wx w Rd (match opc with
           | 0 => Word (N.lnot k w) w
           | 2 => Word k w
           | _ => <{({xr w Rd} & {N.lnot (N.shiftl 65535 p mod 2^w) w}#w) | k#w}>
           end).

Definition bfm_il sf opc N_ immr imms Rn Rd := (* C6.2: SBFM, BFM, UBFM (FIX S4, S5) *)
  let w := ds sf in
  match DecodeBitMasks N_ imms immr false w with
  | None => UNDEF
  | Some (wm, tm) =>
      let src := xr w Rn in
      let dst := match opc with 0 => <{scast w (src[imms])}> | 1 => xr w Rd | _ => Word 0 w end in
      let bot := <{ {shift_exp w 3 src (Word immr w)} & wm#w }> in
      let bot := if opc =? 1 then <{(dst & {N.lnot wm w}#w) | bot}> else bot in
      wx w Rd <{(dst & {N.lnot tm w}#w) | (bot & tm#w)}>
  end.


(* branches, exception generating and system *)

Definition pstate_il op1 op2 := (* CFINV, XAFLAG, AXFLAG; other MSR (immediate) not modelled. FIX D8 *)
  match op1, op2 with
  | 0, 0 => <{ R_CY := !C }>
  | 0, 1 => <{ R_OV := !C & Z; tmp := C & Z; R_CY := C | Z; R_NG := !C; R_ZR := T }>
  | 0, 2 => <{ R_ZR := Z | V; R_CY := C & !V; R_NG := 0#1; R_OV := 0#1 }>
  | _, _ => Nop
  end.


(* loads and stores *)

Definition ls_il size opc Rn Rt (off: exp) (wback post: bool) := (* C6.2: LDR/STR (single register) *)
  let base := sr 64 Rn in
  let q (wb wu unk: bool) := <{ {spchk Rn}; {xfer size opc Rt (if post then base else <{base + off}>) unk};
                        {if wb then ws 64 Rn (if wu then Unknown 64 else <{base + off}>) else Nop} }> in
  if wback && (Rn =? Rt) && negb (Rn =? 31) then
    CU (if opc =? 0 then [q true false false; q true false true] else [q false false false; q true true false])
  else q wback false false.

Definition lsp_il opc L Rn Rt Rt2 imm7 (wback post: bool) := (* C6.2: STP, LDP, LDPSW, STNP, LDNP, STGP *)
  let stgp := (opc =? 1) && (L =? 0) in
  let sz := if (opc =? 0) || (opc =? 1) && (L =? 1) then 2 else 3 in
  let op := if L =? 0 then 0 else if opc =? 1 then 2 else 1 in
  let off := Word (N.shiftl (scast 7 64 imm7) (if stgp then 4 else sz) mod 2^64) 64 in
  let base := sr 64 Rn in
  let q (wb wu u1 u2: bool) := <{ {spchk Rn}; tmp := {if post then base else <{base + off}>}; (* FIX S16 *)
     {xfer sz op Rt T u1}; {xfer sz op Rt2 <{T + {2^sz}#64}> u2};
     {if wb then ws 64 Rn (if wu then Unknown 64 else if post then <{T + off}> else T) else Nop} }> in
  let c1 := wback && ((Rt =? Rn) || (Rt2 =? Rn)) && negb (Rn =? 31) && negb stgp in
  if L =? 0 then
    if c1 then CU [q wback false false false; q wback false (Rt =? Rn) (Rt2 =? Rn)] else q wback false false false
  else
    let q2 (wb wu: bool) := if Rt =? Rt2 then CU [q wb wu true true] else q wb wu false false in
    if c1 then CU [q2 false false; q2 wback true] else q2 wback false.

Definition stx_il size (pair: bool) Rs Rn Rt Rt2 := (* C6.2: STXR, STLXR, STXP, STLXP (FIX S17, S19) *)
  let w := 8 * 2^size in let b := if pair then 2 * 2^size else 2^size in
  let data := if pair then <{ {xr w Rt2} ++ {xr w Rt} }> else xr w Rt in
  let q (ru rnu: bool) := <{ {spchk Rn};
    if unknown 1 then {wx 64 Rs <{1#64}>} (* store not attempted *)
    else {st (if rnu then Unknown 64 else sr 64 Rn) b (if ru then Unknown (8 * b) else data)};
         {wx 64 Rs <{ucast 64 (unknown 1)}>} end }> in
  let q1 (ru: bool) := if (Rs =? Rn) && negb (Rn =? 31) then CU [q ru true; q ru false] else q ru false in
  if (Rs =? Rt) || pair && (Rs =? Rt2) then CU [q1 true; q1 false] else q1 false.

Definition cas_il sz (pair: bool) Rs Rn Rt := (* C6.2: CAS, CASP (FIX S14) *)
  let w := 8 * 2^sz in let b := if pair then 2 * 2^sz else 2^sz in
  let v r := if pair then <{ {xr w (r + 1)} ++ {xr w r} }> else xr w r in
  if pair && (N.odd Rs || N.odd Rt) then UNDEF else
  <{ {spchk Rn}; tmp := {ld (sr 64 Rn) b};
     if T = {v Rs} then {st (sr 64 Rn) b (v Rt)} else nop end;
     {if pair then Seq (wx w Rs <{T[{w-1}:0]}>) (wx w (Rs + 1) <{T[{2*w-1}:w]}>) else wx w Rs T} }>.

Definition atomic_il op size Rs Rn Rt := (* C6.2: LD<op>, SWP (FIX D7, S18) *)
  let w := 8 * 2^size in let a := sr 64 Rn in let v := xr w Rs in
  let r := match op with
           | AT_ADD => <{T + v}> | AT_CLR => <{T & !v}> | AT_EOR => <{T ^ v}> | AT_SET => <{T | v}>
           | AT_SMAX => <{ite (v s< T) T v}> | AT_SMIN => <{ite (v s< T) v T}>
           | AT_UMAX => <{ite (v < T) T v}> | AT_UMIN => <{ite (v < T) v T}> | AT_SWP => v
           end in
  <{ {spchk Rn}; tmp := {ld a (2^size)}; {st a (2^size) r}; {wx w Rt T} }>.

Definition tag_il opc imm9 op2 Rn Rt := (* C6.2 (Armv8.5 MTE): tag memory is not modelled *)
  let off := Word (N.shiftl (scast 9 64 imm9) 4 mod 2^64) 64 in
  let base := sr 64 Rn in
  if op2 =? 0 then (* LDG: tag access disabled, so Xt's tag becomes 0 (FIX S20) *)
    Seq (spchk Rn) (wx 64 Rt <{ {xr 64 Rt} & {N.lnot (N.shiftl 15 56) 64}#64 }>)
  else let b := 16 * (1 + opc / 2) in (* STG, STZG, ST2G, STZ2G (FIX S21) *)
  <{ {spchk Rn};
     {if N.odd opc then st (if op2 =? 1 then base else <{base + off}>) b (Word 0 (8 * b)) else Nop};
     {if N.odd op2 then ws 64 Rn <{base + off}> else Nop} }>.


(* data processing - register *)

Definition ccmp_il sf op Rm cond imm nzcv Rn := (* C6.2: CCMN, CCMP *)
  let w := ds sf in
  let b i := Word (N.b2n (N.testbit nzcv i)) 1 in
  If (ConditionHolds cond)
     (addsub w op true (fun _ => Nop) (xr w Rn) (if imm =? 1 then Word Rm w else xr w Rm) (Word op 1))
     (setflags (b 3) (b 2) (b 1) (b 0)).

Definition csel_il sf op Rm cond o2 Rn Rd := (* C6.2: CSEL, CSINC, CSINV, CSNEG (FIX D8) *)
  let w := ds sf in let m := xr w Rm in
  If (ConditionHolds cond) (wx w Rd (xr w Rn))
     (wx w Rd (match op, o2 with 0, 0 => m | 0, _ => <{m + 1#w}> | _, 0 => <{!m}> | _, _ => <{0#w - m}> end)).

Definition dp1_il sf op Rn Rd := (* C6.2: RBIT, REV16, REV32, REV, CLZ, CLS (FIX S22) *)
  let w := ds sf in let x := xr w Rn in
  wx w Rd (match op with
           | 0 => rev_exp w w 1 x
           | 1 => rev_exp w 16 8 x
           | 2 => rev_exp w 32 8 x
           | 3 => rev_exp w 64 8 x
           | 4 => <{w#w - (width(x))}>
           | _ => <{ucast w ({w-1}#{w-1} - (width(x[{w-1}:1] ^ x[{w-2}:0])))}>
           end).

Definition dp2_il sf op Rm Rn Rd := (* C6.2: UDIV, SDIV, LSLV, LSRV, ASRV, RORV (FIX D8) *)
  let w := ds sf in let x := xr w Rn in let y := xr w Rm in
  wx w Rd (match op with 2 => <{x / y}> | 3 => BinOp OP_SDIVIDE x y | _ => shift_exp w (op - 8) x <{y % w#w}> end).

Definition dp3_il sf op31 Rm o0 Ra Rn Rd := (* C6.2: MADD, MSUB, SMADDL, SMSUBL, SMULH, UMADDL, UMSUBL, UMULH (FIX D8) *)
  let c := if op31 <? 4 then CAST_SIGNED else CAST_UNSIGNED in
  if (op31 =? 2) || (op31 =? 6) then
    wx 64 Rd (Cast CAST_HIGH 64 <{ {Cast c 128 (xr 64 Rn)} * {Cast c 128 (xr 64 Rm)} }>)
  else
    let w := if op31 =? 0 then ds sf else 64 in
    let f r := if op31 =? 0 then xr w r else Cast c 64 (xr 32 r) in
    wx w Rd (BinOp (if o0 =? 0 then OP_PLUS else OP_MINUS) (xr w Ra) <{ {f Rn} * {f Rm} }>).


Definition arm_il (i: arm_inst) : stmt :=
  match i with
  | ARM_UNDEFINED => UNDEF
  | idk => havoc
  | ARM_NOP => Nop
  (* data processing - immediate *)
  | ARM_ADR op lo hi Rd => adr_il op lo hi Rd
  | ARM_addsub_i sf op S_ sh imm Rn Rd => let w := ds sf in (* FIX S10 *)
      addsub w op (S_ =? 1) (if S_ =? 1 then wx w Rd else ws w Rd) (sr w Rn) (Word (N.shiftl imm (12 * sh)) w) (Word op 1)
  | ARM_logic_i sf opc N_ immr imms Rn Rd => logic_i_il sf opc N_ immr imms Rn Rd
  | ARM_movw sf opc hw imm Rd => movw_il sf opc hw imm Rd
  | ARM_bfm sf opc N_ immr imms Rn Rd => bfm_il sf opc N_ immr imms Rn Rd
  | ARM_EXTR sf Rm lsb Rn Rd => let w := ds sf in wx w Rd (Extract (lsb + w - 1) lsb (Concat (xr w Rn) (xr w Rm)))
  (* branches, exception generating and system *)
  | ARM_B_cond cond imm => If (ConditionHolds cond) (Jmp (pcrel imm 21)) Nop
  | ARM_B op imm => if op =? 1 then Seq (wx 64 30 <{PC + 4#64}>) (Jmp (pcrel imm 28)) else Jmp (pcrel imm 28)
  | ARM_br opc Rn => if opc =? 1 then <{ tmp := {xr 64 Rn}; {wx 64 30 <{PC + 4#64}>}; jmp T }> else Jmp (xr 64 Rn)
  | ARM_CBZ sf op imm Rt => If (BinOp (if op =? 0 then OP_EQ else OP_NEQ) (xr (ds sf) Rt) (Word 0 (ds sf))) (Jmp (pcrel imm 21)) Nop
  | ARM_TBZ b5 op b40 imm Rt => If <{ {xr 64 Rt}[{b5 * 32 + b40}] = op#1 }> (Jmp (pcrel imm 16)) Nop
  | ARM_pstate op1 op2 => pstate_il op1 op2
  | ARM_SYSL Rt => wx 64 Rt (Unknown 64)
  (* loads and stores *)
  | ARM_ls size opc Rn Rt off wb post => ls_il size opc Rn Rt (Word off 64) wb post
  | ARM_ls_r size opc Rn Rt Rm opt S_ => ls_il size opc Rn Rt (ext_exp 64 (xr 64 Rm) opt (S_ * size)) false false (* FIX S15 *)
  | ARM_ldr_lit opc imm Rt => xfer (2 + opc mod 2) (if opc =? 2 then 2 else 1) Rt (pcrel imm 21) false
  | ARM_lsp opc L Rn Rt Rt2 imm wb post => lsp_il opc L Rn Rt Rt2 imm wb post
  | ARM_stx size pr Rs Rn Rt Rt2 => stx_il size pr Rs Rn Rt Rt2
  | ARM_cas sz pr Rs Rn Rt => cas_il sz pr Rs Rn Rt
  | ARM_atomic op size Rs Rn Rt => atomic_il op size Rs Rn Rt
  | ARM_tag opc imm op2 Rn Rt => tag_il opc imm op2 Rn Rt
  (* data processing - register *)
  | ARM_logic_r sf opc sh N_ Rm imm Rn Rd => let w := ds sf in
      let y := shift_exp w sh (xr w Rm) (Word imm w) in
      logic_il w opc (xr w Rn) (if N_ =? 1 then <{!y}> else y) (wx w Rd)
  | ARM_addsub_r sf op S_ sh Rm imm Rn Rd => let w := ds sf in (* FIX S8 *)
      addsub w op (S_ =? 1) (wx w Rd) (xr w Rn) (shift_exp w sh (xr w Rm) (Word imm w)) (Word op 1)
  | ARM_addsub_x sf op S_ Rm opt imm Rn Rd => let w := ds sf in
      addsub w op (S_ =? 1) (if S_ =? 1 then wx w Rd else ws w Rd) (sr w Rn) (ext_exp w (xr 64 Rm) opt imm) (Word op 1)
  | ARM_adc sf op S_ Rm Rn Rd => let w := ds sf in addsub w op (S_ =? 1) (wx w Rd) (xr w Rn) (xr w Rm) (Var R_CY)
  | ARM_ccmp sf op Rm cond imm nzcv Rn => ccmp_il sf op Rm cond imm nzcv Rn
  | ARM_csel sf op Rm cond o2 Rn Rd => csel_il sf op Rm cond o2 Rn Rd
  | ARM_dp1 sf op Rn Rd => dp1_il sf op Rn Rd
  | ARM_dp2 sf op Rm Rn Rd => dp2_il sf op Rm Rn Rd
  | ARM_dp3 sf op31 Rm o0 Ra Rn Rd => dp3_il sf op31 Rm o0 Ra Rn Rd
  end.

Definition arm2il (a: addr) (i: arm_inst) : stmt := Seq (Move R_PC (Word (a mod 2^64) 64)) (arm_il i).

Definition arm8_prog : program :=
  fun s a => Some (4, arm2il a (if a mod 4 =? 0 then arm_decode (getmem 64 LittleE 4 (s V_MEM64) a) else ARM_UNDEFINED)).


(********** decoder sanity checks **********)

Example dec_add  : arm_decode 0x91004020 = ARM_addsub_i 1 0 0 0 16 1 0.        Proof. vm_compute. reflexivity. Qed. (* add x0, x1, #16 *)
Example dec_cmp  : arm_decode 0xF100001F = ARM_addsub_i 1 1 1 0 0 0 31.        Proof. vm_compute. reflexivity. Qed. (* cmp x0, #0 *)
Example dec_ldr  : arm_decode 0xF94007E0 = ARM_ls 3 1 31 0 8 false false.      Proof. vm_compute. reflexivity. Qed. (* ldr x0, [sp, #8] *)
Example dec_stp  : arm_decode 0xA9BF7BFD = ARM_lsp 2 0 31 29 30 0x7E true false. Proof. vm_compute. reflexivity. Qed. (* stp x29, x30, [sp, #-16]! *)
Example dec_mov  : arm_decode 0xAA0103E0 = ARM_logic_r 1 1 0 0 1 0 31 0.       Proof. vm_compute. reflexivity. Qed. (* mov x0, x1 *)
Example dec_ret  : arm_decode 0xD65F03C0 = ARM_br 2 30.                        Proof. vm_compute. reflexivity. Qed. (* ret *)
Example dec_nop  : arm_decode 0xD503201F = ARM_NOP.                            Proof. vm_compute. reflexivity. Qed. (* nop *)
Example dec_pac  : arm_decode 0xD503233F = ARM_NOP.                            Proof. vm_compute. reflexivity. Qed. (* paciasp *)
Example dec_sysl : arm_decode 0xD5280000 = ARM_SYSL 0.                         Proof. vm_compute. reflexivity. Qed. (* sysl x0, #0, c0, c0, #0 *)


(********** well-typedness **********)

(* Every lifted instruction starts in c8 (cpu state plus R_PC) and each statement leaves its
   context c unchanged: registers and flags are already typed in c8, and the lifter temporary
   tmp only lives inside one "tmp := e; q" block.  So each IL pattern gets one lemma
   (hastyp_stmt c0 c q c, or hastyp_exp c e w), and the tactics ety/sty just apply them. *)

Local Notation c0 := arm8typctx.
Notation c8 := ((update arm8typctx R_PC (Some 64))).
Definition okc (c: typctx) := c8 ⊆ c.
Lemma ds0 : ds 0 = 32. Proof. reflexivity. Qed.
Lemma ds1 : ds 1 = 64. Proof. reflexivity. Qed.

(* Field ranges that the IL needs; arm_decode only produces these (decode_ok). *)
Definition inst_ok (i: arm_inst) : Prop :=
  match i with
  | ARM_addsub_i sf op _ sh imm _ _ => sf < 2 /\ op < 2 /\ sh < 2 /\ imm < 2^12
  | ARM_logic_i sf _ _ _ _ _ _ | ARM_movw sf _ _ _ _ | ARM_CBZ sf _ _ _ | ARM_adc sf _ _ _ _ _
  | ARM_csel sf _ _ _ _ _ _ | ARM_dp1 sf _ _ _ | ARM_dp2 sf _ _ _ _ | ARM_dp3 sf _ _ _ _ _ _ => sf < 2
  | ARM_bfm sf _ _ immr imms _ _ => sf < 2 /\ immr < ds sf /\ imms < ds sf
  | ARM_EXTR sf _ lsb _ _ => sf < 2 /\ lsb < ds sf
  | ARM_TBZ b5 op b40 _ _ => b5 < 2 /\ op < 2 /\ b40 < 32
  | ARM_ls size opc _ _ off _ _ => size < 4 /\ opc < 4 /\ (opc = 3 -> size < 2) /\ off < 2^64
  | ARM_ls_r size opc _ _ _ _ S_ => size < 4 /\ opc < 4 /\ (opc = 3 -> size < 2) /\ S_ < 2
  | ARM_ldr_lit opc _ _ => opc < 3
  | ARM_lsp opc L _ _ _ _ _ _ => opc < 3 /\ L < 2
  | ARM_stx size _ _ _ _ _ | ARM_atomic _ size _ _ _ | ARM_cas size _ _ _ _ => size < 4
  | ARM_tag opc _ _ _ _ => opc < 4
  | ARM_logic_r sf _ _ _ _ imm _ _ => sf < 2 /\ imm < 2^6
  | ARM_addsub_r sf op _ _ _ imm _ _ => sf < 2 /\ op < 2 /\ imm < 2^6
  | ARM_addsub_x sf op _ _ _ imm _ _ => sf < 2 /\ op < 2 /\ imm < 2^3
  | ARM_ccmp sf op Rm _ _ _ _ => sf < 2 /\ op < 2 /\ Rm < 2^5
  | _ => True
  end.

(* --- variable lookups --- *)

Lemma arm_varid_typ n : c0 (arm_varid n) = Some 64.
Proof. destruct n as [|p]; [reflexivity|]. repeat (reflexivity || destruct p as [p|p|]). Qed.

Definition notreg v := match v with V_MEM64 | R_SP | R_NG | R_ZR | R_CY | R_OV | SCTLR_E1 | V_TEMP _ => True | _ => False end.
Lemma varid_notreg n v : notreg v -> arm_varid n <> v.
Proof. intros H E. subst v. destruct n as [|p]; [exact H|]. repeat (exact H || destruct p as [p|p|]). Qed.

Lemma c8_varid n : c8 (arm_varid n) = Some 64.
Proof. rewrite update_frame by (apply varid_notreg; exact I). apply arm_varid_typ. Qed.

Lemma sub_upd (c: typctx) v x : c v = x -> c ⊆ (update c v x).
Proof. intros H v' y E. unfold update. destruct (v' == v); subst; congruence. Qed.

Lemma sub_upd_none (c: typctx) v x : c v = None -> c ⊆ (update c v x).
Proof. intros H v' y E. unfold update. destruct (v' == v); subst; congruence. Qed.

Lemma okc_tmp c x : okc c -> okc ((update c tmp x)).
Proof. intros OK v y E. unfold update. destruct (_ == _) as [->|NE]; [discriminate E | exact (OK v y E)]. Qed.

(* c[tmp:=..] v = Some w, down to c8 *)
Ltac lk := first
  [ apply update_updated
  | rewrite update_frame; [lk | discriminate]
  | match goal with H: okc _ |- _ => apply H; first [apply c8_varid | reflexivity] end ].
Ltac okt := repeat apply okc_tmp; assumption.

(* --- bounds and arithmetic side conditions --- *)

Lemma DBM_bound a b c d M wm tm : DecodeBitMasks a b c d M = Some (wm, tm) -> wm < 2^M /\ tm < 2^M.
Proof. unfold DecodeBitMasks, Replicate. destruct (_ || _); intro H; inversion H. split; apply mp2_mod_lt. Qed.

Ltac arith := solve [ vm_compute; first [reflexivity | discriminate] | lia ].
Ltac bnd := solve
  [ apply mp2_mod_lt
  | unfold scast; apply ofZ_bound
  | apply xbits_bound
  | apply lnot_bound; bnd
  | match goal with D: DecodeBitMasks _ _ _ _ _ = Some _ |- _ => apply DBM_bound in D; destruct D; assumption end
  | eapply N.lt_le_trans; [ apply shiftl_bound; eassumption | apply N.pow_le_mono_r; [discriminate | arith] ]
  | eapply N.lt_le_trans; [ eassumption | first [ apply N.pow_le_mono_r; [discriminate | arith] | arith ] ]
  | destruct (N.testbit _ _); arith
  | arith ].

(* --- expressions --- *)

Lemma low_typ c w e : hastyp_exp c e 64 -> w <= 64 -> hastyp_exp c (low w e) w.
Proof. intros. unfold low. destruct (N.eqb_spec w 64). subst; assumption. eapply TCast; eassumption. Qed.

Lemma xr_typ c w n : okc c -> 0 < w -> w <= 64 -> hastyp_exp c (xr w n) w.
Proof.
  intros OK W0 W. unfold xr. destruct (n =? 31).
  - apply TWord. apply N.neq_0_lt_0, N.pow_nonzero. discriminate.
  - apply low_typ; [apply TVar, OK, c8_varid | assumption].
Qed.

Lemma sr_typ c w n : okc c -> w <= 64 -> hastyp_exp c (sr w n) w.
Proof. intros OK W. apply low_typ; [|assumption]. apply TVar, OK. destruct (n =? 31); [reflexivity | apply c8_varid]. Qed.

Lemma ld_typ c a b : okc c -> hastyp_exp c a 64 -> b <= 2^64 -> hastyp_exp c (ld a b) (8 * b).
Proof. intros OK A B. unfold ld. rewrite N.mul_comm. eapply TLoad; [exact B | apply TVar, OK; reflexivity | exact A]. Qed.

Lemma zx64_typ c w e : hastyp_exp c e w -> w <= 64 -> hastyp_exp c (zx64 w e) 64.
Proof. intros. unfold zx64. destruct (N.eqb_spec w 64). subst; assumption. eapply TCast; eassumption. Qed.

Lemma hastyp_extract' c e w n1 n2 w' : hastyp_exp c e w -> n1 < w -> N.succ n1 - n2 = w' -> hastyp_exp c (Extract n1 n2 e) w'.
Proof. intros. eapply hastyp_extract; eassumption. Qed.

Lemma hastyp_extract1 c e w n : hastyp_exp c e w -> n < w -> hastyp_exp c (Extract n n e) 1.
Proof. intros. eapply hastyp_extract'; try eassumption. lia. Qed.

Lemma hastyp_concat' c e1 e2 w1 w2 w' : hastyp_exp c e1 w1 -> hastyp_exp c e2 w2 -> w1 + w2 = w' -> hastyp_exp c (Concat e1 e2) w'.
Proof. intros. eapply hastyp_concat; eassumption. Qed.

Lemma ext_typ c w x opt sh : hastyp_exp c x 64 -> 0 < w -> w <= 64 -> sh < 2^w -> hastyp_exp c (ext_exp w x opt sh) w.
Proof.
  intros X W0 W SH. unfold ext_exp.
  eapply hastyp_binop; [reflexivity | | apply TWord, SH].
  eapply TCast; [eapply hastyp_extract'; [exact X | lia | reflexivity] |].
  destruct (opt <? 4); lia.
Qed.

Ltac cty := first
  [ eapply hastyp_concat'; [cty | cty | reflexivity]
  | eapply hastyp_extract'; [eassumption | arith | reflexivity]
  | eassumption ].

Lemma rev_typ c x w cs e :
  hastyp_exp c x w ->
  In (w, cs, e) [(32,32,1); (64,64,1); (32,16,8); (64,16,8); (32,32,8); (64,32,8); (32,64,8); (64,64,8)] ->
  hastyp_exp c (rev_exp w cs e x) w.
Proof.
  intros X H. repeat destruct H as [H|H]; try contradiction; injection H as <- <- <-;
  match goal with |- hastyp_exp _ ?r _ => let t := eval vm_compute in r in change r with t end; cty.
Qed.

(* Evaluate a closed boolean test; otherwise case-split on it. *)
Ltac split_if b := first
  [ let v := eval vm_compute in b in
    match v with true => change b with true | false => change b with false end; cbv beta iota
  | destruct b ].

Ltac split_match x := first
  [ let v := eval vm_compute in x in
    match v with N0 => idtac | Npos _ => idtac end; change x with v; cbv beta iota
  | destruct x ].

Ltac notclosed b := let v := eval vm_compute in b in match v with true => fail 1 | false => fail 1 | _ => idtac end.

Ltac unfold_head e := match e with ?f _ => unfold_head f | _ => unfold e end.

Ltac ety := match goal with
  | |- hastyp_exp _ (xr _ _) _ => apply xr_typ; [okt | arith | arith]
  | |- hastyp_exp _ (sr _ _) _ => apply sr_typ; [okt | arith]
  | |- hastyp_exp _ (ld _ _) _ => apply ld_typ; [okt | ety | arith]
  | |- hastyp_exp _ (zx64 _ _) _ => apply zx64_typ; [ety | arith]
  | |- hastyp_exp _ (ext_exp _ _ _ _) _ => apply ext_typ; [ety | arith | arith | bnd]
  | |- hastyp_exp _ (rev_exp _ _ _ _) _ => apply rev_typ; [ety | cbv [In]; tauto]
  | |- hastyp_exp _ (if ?b then _ else _) _ => split_if b; ety
  | |- hastyp_exp _ (BinOp (if ?b then _ else _) _ _) _ => split_if b; ety
  | |- hastyp_exp _ (Cast (if ?b then _ else _) _ _) _ => split_if b; ety
  | |- hastyp_exp _ (match ?x with _ => _ end) _ => split_match x; ety
  | |- hastyp_exp _ (Var _) _ => apply TVar; lk
  | |- hastyp_exp _ (Word _ _) _ => apply TWord; bnd
  | |- hastyp_exp _ (BinOp _ _ _) _ => eapply hastyp_binop; [reflexivity | ety | ety]
  | |- hastyp_exp _ (UnOp _ _) _ => apply TUnOp; ety
  | |- hastyp_exp _ (Cast _ _ _) _ => eapply TCast; [ety | cbv beta iota; arith]
  | |- hastyp_exp _ (Unknown _) _ => apply TUnknown
  | |- hastyp_exp _ (Ite _ _ _) _ => eapply TIte; [ety | ety | ety]
  | |- hastyp_exp _ (Extract ?n ?n _) _ => eapply hastyp_extract1; [ety | arith]
  | |- hastyp_exp _ (Extract _ _ _) _ => eapply hastyp_extract'; [ety | arith | first [reflexivity | lia]]
  | |- hastyp_exp _ (Concat _ _) _ => eapply hastyp_concat'; [ety | ety | first [reflexivity | lia]]
  | |- hastyp_exp _ ?e _ => unfold_head e; cbv beta iota zeta; rewrite ?ds0, ?ds1; ety
  end.

(* --- statements --- *)

Lemma nop_typ c : hastyp_stmt c0 c Nop c.          Proof. apply TNop, pfsub_refl. Qed.
Lemma exn_typ c i : hastyp_stmt c0 c (Exn i) c.     Proof. apply TExn, pfsub_refl. Qed.
Lemma jmp_typ c e w : hastyp_exp c e w -> hastyp_stmt c0 c (Jmp e) c.
Proof. intro. eapply TJmp; [eassumption | apply pfsub_refl]. Qed.
Lemma seq_typ c q1 q2 : hastyp_stmt c0 c q1 c -> hastyp_stmt c0 c q2 c -> hastyp_stmt c0 c (Seq q1 q2) c.
Proof. intros. eapply TSeq; try eassumption. apply pfsub_refl. Qed.
Lemma if_typ c e q1 q2 : hastyp_exp c e 1 -> hastyp_stmt c0 c q1 c -> hastyp_stmt c0 c q2 c -> hastyp_stmt c0 c (If e q1 q2) c.
Proof. intros. eapply TIf; try eassumption. apply pfsub_refl. Qed.

Lemma move_typ c v w e : okc c -> c0 v = Some w -> c8 v = Some w -> hastyp_exp c e w -> hastyp_stmt c0 c (Move v e) c.
Proof. intros OK V V8 E. eapply TMove; [right; exact V | exact E | apply sub_upd, OK, V8]. Qed.


Lemma wx_typ c w n e : okc c -> hastyp_exp c e w -> w <= 64 -> hastyp_stmt c0 c (wx w n e) c.
Proof.
  intros OK E W. unfold wx. destruct (n =? 31); [apply nop_typ|].
  eapply move_typ; [exact OK | apply arm_varid_typ | apply c8_varid | apply zx64_typ; assumption].
Qed.

Lemma ws_typ c w n e : okc c -> hastyp_exp c e w -> w <= 64 -> hastyp_stmt c0 c (ws w n e) c.
Proof.
  intros OK E W. unfold ws. eapply move_typ; [exact OK | | | apply zx64_typ; eassumption];
  destruct (n =? 31); first [reflexivity | apply arm_varid_typ | apply c8_varid].
Qed.

Lemma st_typ c a b e : okc c -> hastyp_exp c a 64 -> hastyp_exp c e (8 * b) -> b <= 2^64 -> hastyp_stmt c0 c (st a b e) c.
Proof.
  intros OK A E B. unfold st. rewrite N.mul_comm in E.
  apply move_typ with (w := 2^64 * 8); [exact OK | reflexivity | reflexivity |].
  eapply TStore; [exact B | apply TVar, OK; reflexivity | exact A | exact E].
Qed.

Lemma tmp_typ c w e q : okc c -> c tmp = None -> hastyp_exp c e w ->
  hastyp_stmt c0 ((update c tmp (Some w))) q ((update c tmp (Some w))) -> hastyp_stmt c0 c (Seq (Move tmp e) q) c.
Proof.
  intros OK N E Q. eapply TSeq; [eapply TMove; [left; reflexivity | exact E | apply pfsub_refl] | exact Q |].
  apply sub_upd_none, N.
Qed.

Lemma CU_typ c alts : Forall (fun q => hastyp_stmt c0 c q c) alts -> hastyp_stmt c0 c (CU alts) c.
Proof.
  intro H. unfold CU, UNDEF.
  assert (H': Forall (fun q => hastyp_stmt c0 c q c) (Exn 4 :: alts)) by (constructor; [apply exn_typ | exact H]).
  clear H. induction H'; simpl. apply nop_typ. apply if_typ; [apply TUnknown | assumption | assumption].
Qed.

Ltac sty := match goal with
  | |- hastyp_stmt _ _ ?q _ => match q with context [if ?b then _ else _] => notclosed b; destruct b end; sty
  | |- hastyp_stmt _ _ (wx _ _ _) _ => apply wx_typ; [okt | ety | arith]
  | |- hastyp_stmt _ _ (ws _ _ _) _ => apply ws_typ; [okt | ety | arith]
  | |- hastyp_stmt _ _ (st _ _ _) _ => apply st_typ; [okt | ety | ety | arith]
  | |- hastyp_stmt _ _ (CU _) _ => apply CU_typ; repeat constructor; sty
  | |- hastyp_stmt _ _ (Seq (Move tmp _) _) _ => eapply tmp_typ; [okt | assumption | ety | sty]
  | |- hastyp_stmt _ _ (Move _ _) _ => eapply move_typ; [okt | reflexivity | reflexivity | ety]
  | |- hastyp_stmt _ _ (Seq _ _) _ => apply seq_typ; sty
  | |- hastyp_stmt _ _ (If _ _ _) _ => apply if_typ; [ety | sty | sty]
  | |- hastyp_stmt _ _ Nop _ => apply nop_typ
  | |- hastyp_stmt _ _ (Exn _) _ => apply exn_typ
  | |- hastyp_stmt _ _ (Jmp _) _ => eapply jmp_typ; ety
  | |- hastyp_stmt _ _ (match DecodeBitMasks ?a ?b ?c ?d ?e with _ => _ end) _ =>
      destruct (DecodeBitMasks a b c d e) as [[? ?]|] eqn:?; cbv beta iota; sty
  | |- hastyp_stmt _ _ (if ?b then _ else _) _ => split_if b; sty
  | |- hastyp_stmt _ _ ((if ?b then _ else _) _) _ => split_if b; sty
  | |- hastyp_stmt _ _ ((fun _ => _) _) _ => cbv beta; sty
  | |- hastyp_stmt _ _ (match ?x with _ => _ end) _ => split_match x; sty
  | |- hastyp_stmt _ _ ?q _ => unfold_head q; cbv beta iota zeta; rewrite ?ds0, ?ds1; sty
  end.

(* --- instructions --- *)


Ltac cases := repeat match goal with
  | H: _ /\ _ |- _ => destruct H
  | H: ?x < 2 |- _ => assert (x = 0 \/ x = 1) as [->| ->] by lia; clear H
  | H: ?x < 3 |- _ => assert (x = 0 \/ x = 1 \/ x = 2) as [->|[->| ->]] by lia; clear H
  | H: ?x < 4 |- _ => assert (x = 0 \/ x = 1 \/ x = 2 \/ x = 3) as [->|[->|[->| ->]]] by lia; clear H
  | H: ?x = ?x -> _ |- _ => specialize (H eq_refl)
  | H: _ = _ -> _ |- _ => clear H
  end; rewrite ?ds0, ?ds1 in *; try (exfalso; lia).

Lemma arm_il_typ c i : okc c -> c tmp = None -> inst_ok i -> hastyp_stmt c0 c (arm_il i) c.
Proof.
  intros OK TN I. destruct i; cbv [inst_ok] in I; unfold arm_il; cases; cbv beta iota; sty.
Qed.

Theorem arm2il_welltyped a i : inst_ok i -> hastyp_stmt c0 c0 (arm2il a i) c8.
Proof.
  intro I. eapply TSeq; [eapply TMove; [left; reflexivity | apply TWord, mp2_mod_lt | apply pfsub_refl] | | apply pfsub_refl].
  apply arm_il_typ; [apply pfsub_refl | reflexivity | exact I].
Qed.

(* --- the decoder only produces inst_ok instructions --- *)

Lemma uimm_bound a s : a < 2^12 -> s < 4 -> N.shiftl a s < 2^64.
Proof. intros A S4. eapply N.lt_le_trans; [apply shiftl_bound, A | apply N.pow_le_mono_r; [discriminate | lia]]. Qed.

(* Turn boolean tests from the decoder's if-tree into arithmetic facts. *)
Ltac dsplit := repeat match goal with
  | H: (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
  | H: (_ || _) = false |- _ => apply orb_false_iff in H as [? ?]
  | H: (_ && _) = false |- _ => apply andb_false_iff in H as [?|?]
  | H: (_ || _) = true |- _ => apply orb_true_iff in H as [?|?]
  | H: negb _ = true |- _ => apply negb_true_iff in H
  | H: negb _ = false |- _ => apply negb_false_iff in H
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  | H: (_ <? _) = true |- _ => apply N.ltb_lt in H
  | H: (_ <? _) = false |- _ => apply N.ltb_ge in H
  | H: (_ <=? _) = true |- _ => apply N.leb_le in H
  | H: (_ <=? _) = false |- _ => apply N.leb_gt in H
  end.

(* Replace each field xbits n i j by a variable bounded by 2^(j-i). *)
Ltac xb1 n i j := let k := eval vm_compute in (2^(j-i)) in
  let H := fresh in pose proof (xbits_bound n i j : xbits n i j < k) as H;
  generalize dependent (xbits n i j); intros.
Ltac xb := repeat match goal with
  | |- context [xbits ?n ?i ?j] => xb1 n i j
  | _: context [xbits ?n ?i ?j] |- _ => xb1 n i j
  end.

Ltac leaf := cbv beta iota delta [inst_ok]; repeat split; intros; try exact I;
  try solve [ apply xbits_bound | unfold scast; apply ofZ_bound | apply uimm_bound; apply xbits_bound | arith
            | eapply N.lt_le_trans; [apply xbits_bound | arith] ];
  unfold ds in *; dsplit; xb;
  repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:? end; dsplit; lia.

(* Sub-decoders: split their tests, keeping the facts the leaves need. *)
Ltac dtree := cbv beta zeta; repeat match goal with
  | |- inst_ok (if ?b then _ else _) => destruct b eqn:?
  | |- inst_ok (match ?x with _ => _ end) => destruct x
  end; leaf.

Lemma dp_imm_ok n : inst_ok (dp_imm n).            Proof. unfold dp_imm; dtree. Qed.
Lemma exc_gen_ok n : inst_ok (exc_gen n).          Proof. unfold exc_gen; dtree. Qed.
Lemma barriers_ok n : inst_ok (barriers n).        Proof. unfold barriers; dtree. Qed.
Lemma uncond_b_reg_ok n : inst_ok (uncond_b_reg n). Proof. unfold uncond_b_reg; dtree. Qed.
Lemma ls_imm_ok n f : inst_ok (ls_imm n f).        Proof. unfold ls_imm, ls_simd; dtree. Qed.
Lemma ls_uimm_ok n : inst_ok (ls_uimm n).          Proof. unfold ls_uimm, ls_simd; dtree. Qed.
Lemma ls_reg_ok n : inst_ok (ls_reg n).            Proof. unfold ls_reg, ls_simd; dtree. Qed.
Lemma ldr_lit_ok n : inst_ok (ldr_lit n).          Proof. unfold ldr_lit; dtree. Qed.
Lemma ldst_pair_ok n : inst_ok (ldst_pair n).      Proof. unfold ldst_pair; dtree. Qed.
Lemma ldst_excl_ok n : inst_ok (ldst_excl n).      Proof. unfold ldst_excl; dtree. Qed.
Lemma atomic_ok n : inst_ok (atomic n).            Proof. unfold atomic; dtree. Qed.
Lemma ldst_tags_ok n : inst_ok (ldst_tags n).      Proof. unfold ldst_tags; dtree. Qed.
Lemma dp1_ok n : inst_ok (dp1 n).                  Proof. unfold dp1; dtree. Qed.
Lemma dp2_ok n : inst_ok (dp2 n).                  Proof. unfold dp2; dtree. Qed.
Lemma dp3_ok n : inst_ok (dp3 n).                  Proof. unfold dp3; dtree. Qed.

(* Encoding tables: their row tests carry no facts the leaves need, so split them without
   remembering anything and close each leaf with a sub-decoder lemma or leaf. *)
Ltac ttree := cbv beta zeta; repeat match goal with
  | |- inst_ok (if ?b then _ else _) => destruct b
  end; lazymatch goal with
  | |- inst_ok (dp_imm _) => apply dp_imm_ok        | |- inst_ok (exc_gen _) => apply exc_gen_ok
  | |- inst_ok (barriers _) => apply barriers_ok    | |- inst_ok (uncond_b_reg _) => apply uncond_b_reg_ok
  | |- inst_ok (ls_imm _ _) => apply ls_imm_ok      | |- inst_ok (ls_uimm _) => apply ls_uimm_ok
  | |- inst_ok (ls_reg _) => apply ls_reg_ok        | |- inst_ok (ldr_lit _) => apply ldr_lit_ok
  | |- inst_ok (ldst_pair _) => apply ldst_pair_ok  | |- inst_ok (ldst_excl _) => apply ldst_excl_ok
  | |- inst_ok (atomic _) => apply atomic_ok        | |- inst_ok (ldst_tags _) => apply ldst_tags_ok
  | |- inst_ok (dp1 _) => apply dp1_ok              | |- inst_ok (dp2 _) => apply dp2_ok
  | |- inst_ok (dp3 _) => apply dp3_ok              | |- _ => leaf
  end.

Lemma branch_sys_ok n : inst_ok (branch_sys n).    Proof. unfold branch_sys; ttree. Qed.
Lemma load_store_ok n : inst_ok (load_store n).    Proof. unfold load_store; ttree. Qed.
Lemma dp_reg_ok n : inst_ok (dp_reg n).            Proof. unfold dp_reg; ttree. Qed.

Lemma decode_ok n : inst_ok (arm_decode n).
Proof.
  unfold arm_decode; cbv beta zeta; repeat match goal with |- inst_ok (if ?b then _ else _) => destruct b end.
  all: lazymatch goal with
  | |- inst_ok (dp_imm _) => apply dp_imm_ok   | |- inst_ok (branch_sys _) => apply branch_sys_ok
  | |- inst_ok (load_store _) => apply load_store_ok | |- inst_ok (dp_reg _) => apply dp_reg_ok
  | |- _ => exact I end.
Qed.

Theorem welltyped_arm8_prog : welltyped_prog arm8typctx arm8_prog.
Proof.
  intros s a. exists c8. apply arm2il_welltyped. destruct (_ =? 0); [apply decode_ok | exact I].
Qed.

(* ===================================================================================
   Deviations from armv8_lifter_rework.v (manual: DDI0487E.a)

   Decoder
   D1  hints: the "- -" (HINT) row came first, so every hint matched it and the specific rows
       were dead.  All hint-space instructions (NOP, YIELD, PAC*/AUT* hints, BTI, ...) are NOPs
       when the feature is absent, so the hint space now decodes to ARM_NOP.
   D2  PSTATE: the "MSR (immediate)" row (Rt=11111) came before CFINV/XAFLAG/AXFLAG, so they were
       never decoded.
   D3  LDURSB: opc=10/11 were swapped (opc=10 is the 64-bit variant; C6 LDURSB).
   D4  Load/store (unsigned immediate) was decoded with wback=true, postindex=true (post-index with
       writeback) and imm12 was not scaled by the access size (LDRSH/LDRSB scaled by 2 always).
       Now: offset = imm12 << size, no writeback.
   D5  STLXP 32-bit, STLLR 32-bit and STLR 32-bit passed size 64.
   D6  Atomic table rows "0 0 1 0 0 001" / "1 0 1 1 0 000" had 1-character size patterns
       (worked only because of row order); the table is now decoded from its fields.
   D7  LDUMAXB had no arm2il case (havoc).
   D8  Decoded but never lifted (fell into havoc): LSLV/LSRV/ASRV/RORV, UDIV/SDIV (ARM_SHIFT was never
       produced), CSEL/CSINC/CSINV/CSNEG, MADD/MSUB/[SU]MADDL/[SU]MSUBL/[SU]MULH, EXTR, barriers,
       CFINV/XAFLAG/AXFLAG.  All are lifted now.
   D9  LDAXP was havoc while LDXP was lifted; both now lift as an LDP with zero offset.

   Semantics
   S1  UNDEF was "X14 := PC-4" (an AArch32 idiom; X14 is not a link register in A64 and execution
       continued).  Now Exn 4, the same as unallocated encodings.
   S2  Register 31 as ZR was read as the variable R_XZR and written by many instructions (e.g. CMP,
       ANDS, MOVZ/MOVK, ADR, loads), so "XZR" could become nonzero.  Reads are now the constant 0
       and writes are dropped (the riscv.v r0 idiom).
   S3  Base register Rn=31 must be SP for every load/store; LDUR/STUR, LDR/STR (imm, reg),
       LDTR/STTR, LDAPUR/STLUR, LDXR/LDAR/STLR, STNP/LDNP, atomics, CAS, LDRAA, STG... used XZR.
   S4  SBFM/BFM/UBFM wrote SP when Rd=31 (it is XZR).
   S5  SBFM: top bits were 0 for sf=0; the manual uses top = Replicate(src<S>) for both sizes.
   S6  AddWithCarry: Z was NOT(result=0); C was wrong when carry_in=1 and result=x (e.g. CMP x,#0
       gave C=0); V had a spurious "(result = ones) & carry_in" term.
   S7  arm_data_il wrote either the flags or the destination, never both, so ADDS/SUBS/ADCS/
       ANDS/... lost their result.
   S8  ADD/SUB (shifted register) wrote Rn instead of Rd.
   S9  ADD/SUB (extended register): ExtendReg2's datasize/shift arguments were swapped (operand was
       always Unknown); Rn=31 redirected the write to XZR; Rd=31 must be SP when S=0.
   S10 ADD/SUB (immediate): Rd=31 must be SP when S=0.
   S11 ANDS/BICS (shifted register) set Unknown flags (BICS set none); ADCS/SBCS set Unknown flags.
   S12 Reserved bitmask immediates (DecodeBitMasks) silently gave 0; they are UNDEFINED.
   S13 STLUR stored the base register X[n] instead of X[t].
   S14 CASP compared memory against X[n]:X[n+1] instead of X[s]:X[s+1].
   S15 LDRH/STRH/LDRSH (register) ignored S (offset not scaled by 2).
   S16 LDP/LDNP/LDXP computed the second address after writing Rt (ldp x0, x1, [x0]).
   S17 STXR with Rs=Rt (Rs<>Rn): both CONSTRAINED UNPREDICTABLE branches used rt_unknown=false.
   S18 Atomics tested Xt=?32 (never true; meant 31), so they wrote XZR.
   S19 STXP computed the SP alignment check but never emitted it.
   S20 LDG overwrote Xt with the address; it only replaces Xt's tag bits.
   S21 STZG/STZ2G zeroed 4/8 bytes (LOG2_TAG_GRANULE used as a byte count) instead of 16/32.
   S22 RBIT/REV*/CLZ/CLS returned UNKNOWN (REV16 64-bit even zeroed the top 48 bits); now exact.
   S23 SUBP (unreachable) used Xn for both operands and added; dropped since SUBP stays unmodelled.

   Still open (proposals, not changed here)
   P1  FP/SIMD encodings were UDF (Exn 4); they are now idk (havoc), as they are valid instructions.
   P2  SVC/HVC/BRK/... are havoc; consider a dedicated exception number for SVC as in armv7 (Exn 8).
   P3  FEAT_PAuth is not implemented: hint-space PAC instructions (PACIASP, AUTIASP, ...) are NOPs,
       and LDRAA/LDRAB, BRAA/BLRAA/RETAA/ERETAA, PAC*/AUT*/XPAC* and PACGA are UNDEFINED.
   P4  No alignment faults for exclusives/atomics/CAS (the manual requires aligned addresses).
   P5  MRS/MSR (register) are not modelled (e.g. NZCV, TPIDR_EL0).
   =================================================================================== *)
