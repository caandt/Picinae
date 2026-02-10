open Picinae_armv7_lifter

(** val coq_Z_popcount : int -> int **)

let coq_Z_popcount = (fun z -> bitb z 0 + bitb z 1 + bitb z 2 + bitb z 3 + bitb z 4 + bitb z 5 + bitb z 6 + bitb z 7 + bitb z 8 + bitb z 9 + bitb z 10 + bitb z 11 + bitb z 12 + bitb z 13 + bitb z 14 + bitb z 15 + bitb z 16 + bitb z 17 + bitb z 18 + bitb z 19 + bitb z 20 + bitb z 21 + bitb z 22 + bitb z 23 + bitb z 24 + bitb z 25 + bitb z 26 + bitb z 27 + bitb z 28 + bitb z 29 + bitb z 30 + bitb z 31)

(** val apply_hash : int -> int -> int -> int **)

let apply_hash sl sr z =
  (lsr) ((land) ((lsl) z sl) ((fun x -> ((lsl) 1 x)-1) 32)) sr

(** val tbl_contains : int -> int list -> bool **)

let tbl_contains = (fun a b -> Hashtbl.mem b a)

(** val tbl_add : int list -> int -> int -> int list **)

let tbl_add = (fun tbl a b -> (Hashtbl.add tbl a (); if a <> b then Hashtbl.add tbl b () else (); tbl))

(** val validhash : int list -> int list -> int list -> int -> int -> bool **)

let rec validhash tbl dis dis' sl sr =
  match dis with
  | [] -> true
  | a::t ->
    (match dis' with
     | [] -> true
     | a'::t' ->
       let ha = apply_hash sl sr a in
       let ha' = apply_hash sl sr a' in
       if if tbl_contains ha tbl then true else tbl_contains ha' tbl
       then false
       else validhash (tbl_add tbl ha ha') t t' sl sr)

(** val find_sr : int list -> int list -> int -> int -> int option **)

let rec find_sr dis dis' sl sr =
  if (<=) sr 0
  then None
  else if (fun f dis -> let seen = Hashtbl.create (List.length dis) in f seen dis)
            validhash dis dis' sl sr
       then Some sr
       else find_sr dis dis' sl ((-) sr 1)

(** val find_hash : int list -> int list -> int -> (int * int) option **)

let rec find_hash dis dis' sl =
  if (<=) sl 2
  then None
  else (match find_sr dis dis' sl 31 with
        | Some z -> Some (sl,z)
        | None -> find_hash dis dis' ((-) sl 1))

(** val make_jump_table_map :
    int list -> int list -> int -> int -> (int -> int) -> int -> int **)

let rec make_jump_table_map dis dis' sl sr f =
  match dis with
  | [] -> f
  | di::t ->
    (match dis' with
     | [] -> f
     | di'::t' ->
       let j = apply_hash sl sr di in
       let k = apply_hash sl sr di' in
       let f' = make_jump_table_map t t' sl sr f in
       (fun tbl j k d -> Hashtbl.add tbl j d; Hashtbl.add tbl k d; tbl) f' j
         k (( * ) di' 4))

(** val coq_PC : int **)

let coq_PC =
  15

(** val coq_LR : int **)

let coq_LR =
  14

(** val coq_SP : int **)

let coq_SP =
  13

(** val coq_ALIGN : int -> arm_inst **)

let coq_ALIGN rt =
  ARM_data_i (ARM_BIC, 14, 0, rt, rt, 3)

(** val coq_STR : int -> int -> int -> arm_inst **)

let coq_STR rt rn offset =
  let u = if (<) offset 0 then 0 else 1 in
  ARM_ls_i (ARM_STR, 14, 1, u, 0, rn, rt, ((abs) offset))

(** val coq_LDR : int -> int -> int -> arm_inst **)

let coq_LDR rt rn offset =
  let u = if (<) offset 0 then 0 else 1 in
  ARM_ls_i (ARM_LDR, 14, 1, u, 0, rn, rt, ((abs) offset))

(** val coq_MOVW : int -> int -> int -> arm_inst **)

let coq_MOVW c rd imm =
  ARM_MOV_WT (true, c, ((land) ((lsr) imm 12) 15), rd, ((land) imm 4095))

(** val coq_MOVT : int -> int -> int -> arm_inst **)

let coq_MOVT c rd imm =
  ARM_MOV_WT (false, c, ((land) ((lsr) imm 12) 15), rd, ((land) imm 4095))

(** val coq_MOV : int -> int -> arm_inst **)

let coq_MOV rd rm =
  ARM_data_r (ARM_MOV, 14, 0, 0, rd, 0, 0, rm)

(** val coq_LSL : int -> int -> int -> arm_inst **)

let coq_LSL rd rm imm =
  ARM_data_r (ARM_MOV, 14, 0, 0, rd, imm, 0, rm)

(** val coq_STMDB2 : int -> int -> int -> arm_inst **)

let coq_STMDB2 rn r0 r1 =
  ARM_lsm (ARM_STMDB, 14, 0, rn, ((lor) ((lsl) 1 r0) ((lsl) 1 r1)))

(** val coq_LDMDB2 : int -> int -> int -> arm_inst **)

let coq_LDMDB2 rn r0 r1 =
  ARM_lsm (ARM_LDMDB, 14, 0, rn, ((lor) ((lsl) 1 r0) ((lsl) 1 r1)))

(** val coq_STMDB3 : int -> int -> int -> int -> arm_inst **)

let coq_STMDB3 rn r0 r1 r2 =
  ARM_lsm (ARM_STMDB, 14, 0, rn,
    ((lor) ((lor) ((lsl) 1 r0) ((lsl) 1 r1)) ((lsl) 1 r2)))

(** val coq_LDMDB3 : int -> int -> int -> int -> arm_inst **)

let coq_LDMDB3 rn r0 r1 r2 =
  ARM_lsm (ARM_LDMDB, 14, 0, rn,
    ((lor) ((lor) ((lsl) 1 r0) ((lsl) 1 r1)) ((lsl) 1 r2)))

(** val coq_UBFX : int -> int -> int -> int -> arm_inst **)

let coq_UBFX rd rn sl sr =
  ARM_bfx (false, 14, ((-) 31 sr), rd, ((-) sr sl), rn)

(** val coq_GOTO : int -> int -> int -> arm_inst **)

let coq_GOTO cond src dest =
  let offset = (-) ((-) dest src) 2 in
  let imm = (land) offset ((fun x -> ((lsl) 1 x)-1) 24) in ARM_B (cond, imm)

(** val arm_add : int -> int -> arm_inst list **)

let arm_add reg imm =
  let a = fun x -> ARM_data_i (ARM_ADD, 14, 0, reg, reg, x) in
  (a ((lor) ((lsl) 4 8) (zxbits imm 24 32)))::((a
                                                 ((lor) ((lsl) 8 8)
                                                   (zxbits imm 16 24)))::(
  (a ((lor) ((lsl) 12 8) (zxbits imm 8 16)))::((a (zxbits imm 0 8))::[])))

(** val arm_table_lookup : int -> int -> int -> int -> arm_inst list **)

let arm_table_lookup ti sl sr reg =
  List.append ((coq_UBFX reg reg ((-) sl 2) sr)::((coq_LSL reg reg 2)::[]))
    (List.append (arm_add reg (( * ) 4 ti)) ((coq_LDR reg reg 0)::[]))

type coq_IRM = int -> int -> int -> int -> int -> int list option

type coq_TableCache = int list -> ((int * int) * int) option

type coq_NewInst = ((int list * int list) * coq_TableCache) option

(** val wo_table : int list option -> coq_TableCache -> coq_NewInst **)

let wo_table z' tc =
  match z' with
  | Some z'0 -> Some ((z'0,[]),tc)
  | None -> None

(** val invert_cond : int -> int **)

let invert_cond cond =
  if (=) ((fun x y -> ((x mod y) + y) mod y) cond 2) 0
  then (+) cond 1
  else (-) cond 1

(** val arm_assemble_all_cond : arm_inst list -> int -> int list option **)

let arm_assemble_all_cond insts cond =
  let jump_after = ARM_B ((invert_cond cond), ((-) ( (List.length insts)) 1))
  in
  if (<) cond 14
  then arm_assemble_all (jump_after::insts)
  else arm_assemble_all insts

(** val list_eqb : int list -> int list -> bool **)

let rec list_eqb l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _::_ -> false)
  | a::b ->
    (match l2 with
     | [] -> false
     | c::d -> if (=) a c then list_eqb b d else false)

(** val rewrite_w_table :
    coq_IRM -> coq_TableCache -> int list -> (int -> int) -> int -> int ->
    int -> int -> coq_NewInst **)

let rewrite_w_table irm tc dis i2i' cond i ti ai =
  match tc dis with
  | Some p ->
    let p0,sr = p in
    let ti0,sl = p0 in
    (match irm cond i ti0 sl sr with
     | Some irm0 -> Some ((irm0,[]),tc)
     | None -> None)
  | None ->
    let dis' = List.map i2i' dis in
    (match find_hash dis dis' 31 with
     | Some p ->
       let sl,sr = p in
       (match irm cond i ti sl sr with
        | Some irm0 ->
          let table =
            (fun mjtm dis dis' ai sl sr n ->
  let m = mjtm dis dis' sl sr (Hashtbl.create (2*n)) in
  List.init n (fun x -> match Hashtbl.find_opt m x with | Some y -> y | _ -> ai * 4)
)
              make_jump_table_map dis dis' ai sl sr ((lsl) 1 ((-) 32 sr))
          in
          let tc' = fun x ->
            if list_eqb x dis then Some ((ti,sl),sr) else tc x
          in
          if (>=) ((+) ti ( (List.length table))) ((lsl) 1 30)
          then None
          else Some ((irm0,table),tc')
        | None -> None)
     | None -> None)

(** val coq_MOVWT : int -> int -> int -> arm_inst list **)

let coq_MOVWT c reg a =
  (coq_MOVW c reg ((land) a 0xffff))::((coq_MOVT c reg
                                         ((land) ((lsr) a 16) 0xffff))::[])

(** val cd : int -> int **)

let cd cond =
  if (<) cond 14 then 1 else 0

(** val bx_blx_irm : bool -> int -> int -> coq_IRM **)

let bx_blx_irm l lr reg cond _ ti sl sr =
  arm_assemble_all_cond
    (List.append (if l then coq_MOVWT 14 coq_LR lr else [])
      (List.append (arm_table_lookup ti sl sr reg) ((ARM_BX (14, reg))::[])))
    cond

(** val rewrite_bx_blx :
    bool -> int -> int -> coq_TableCache -> int list -> (int -> int) -> int
    -> int -> int -> int -> coq_NewInst **)

let rewrite_bx_blx l lr reg =
  rewrite_w_table (bx_blx_irm l lr reg)

(** val rewrite_bx :
    int -> coq_TableCache -> int list -> (int -> int) -> int -> int -> int ->
    int -> coq_NewInst **)

let rewrite_bx reg =
  rewrite_bx_blx false 0 reg

(** val rwl_bx : int -> int **)

let rwl_bx c =
  (+) (cd c) 8

(** val rewrite_blx :
    int -> int -> coq_TableCache -> int list -> (int -> int) -> int -> int ->
    int -> int -> coq_NewInst **)

let rewrite_blx lr reg =
  rewrite_bx_blx true lr reg

(** val rwl_blx : int -> int **)

let rwl_blx c =
  (+) (cd c) 10

(** val ldm_pc_irm :
    arm_memm_op -> int -> int -> int -> arm_inst -> coq_IRM **)

let ldm_pc_irm op rn register_list reg orig_inst cond _ ti sl sr =
  let bc =
    ( * ) 4
      (coq_Z_popcount ((land) register_list ((fun x -> ((lsl) 1 x)-1) 16)))
  in
  let offset = (-) ((+) (arm_lsm_op_start op bc) bc) 4 in
  arm_assemble_all_cond
    (List.append ((coq_STR reg coq_SP (-4))::((coq_LDR reg rn offset)::[]))
      (List.append (arm_table_lookup ti sl sr reg)
        ((coq_STR reg rn offset)::((coq_LDR reg coq_SP (-4))::(orig_inst::[])))))
    cond

(** val rewrite_ldm_pc :
    arm_memm_op -> int -> int -> int -> arm_inst -> coq_TableCache -> int
    list -> (int -> int) -> int -> int -> int -> int -> coq_NewInst **)

let rewrite_ldm_pc op rn register_list reg orig_inst =
  rewrite_w_table (ldm_pc_irm op rn register_list reg orig_inst)

(** val rwl_ldm : int -> int **)

let rwl_ldm c =
  (+) (cd c) 12

(** val pc_irm : arm_inst -> int -> coq_IRM **)

let pc_irm sanitized_inst reg cond i ti sl sr =
  let a = (+) (( * ) 4 i) 8 in
  arm_assemble_all_cond
    (List.append
      ((coq_STR reg coq_SP (-4))::((coq_MOVW 14 reg ((land) a 0xffff))::(
      (coq_MOVT 14 reg ((land) ((lsr) a 16) 0xffff))::(sanitized_inst::[]))))
      (List.append (arm_table_lookup ti sl sr reg)
        ((coq_ALIGN coq_SP)::((coq_STR reg coq_SP (-8))::((coq_LDR reg coq_SP
                                                            (-4))::((coq_LDR
                                                                    coq_PC
                                                                    coq_SP
                                                                    (-8))::[]))))))
    cond

(** val pc_sp_irm : arm_inst -> int -> int -> coq_IRM **)

let pc_sp_irm sanitized_inst reg reg2 cond i ti sl sr =
  let a = (+) (( * ) 4 i) 8 in
  arm_assemble_all_cond
    (List.append
      ((coq_STMDB3 coq_SP reg reg2 coq_PC)::((coq_MOV reg2 coq_SP)::(
      (coq_MOVW 14 reg ((land) a 0xffff))::((coq_MOVT 14 reg
                                              ((land) ((lsr) a 16) 0xffff))::(sanitized_inst::[])))))
      (List.append (arm_table_lookup ti sl sr reg)
        ((coq_STR reg reg2 (-4))::((coq_LDMDB3 reg2 reg reg2 coq_PC)::[]))))
    cond

(** val rewrite_pc :
    arm_inst -> int -> coq_TableCache -> int list -> (int -> int) -> int ->
    int -> int -> int -> coq_NewInst **)

let rewrite_pc sanitized_inst reg =
  rewrite_w_table (pc_irm sanitized_inst reg)

(** val rewrite_pc_sp :
    arm_inst -> int -> int -> coq_TableCache -> int list -> (int -> int) ->
    int -> int -> int -> int -> coq_NewInst **)

let rewrite_pc_sp sanitized_inst reg reg2 =
  rewrite_w_table (pc_sp_irm sanitized_inst reg reg2)

(** val rewrite_pc_no_jump :
    arm_inst -> int -> int -> int -> coq_TableCache -> coq_NewInst **)

let rewrite_pc_no_jump sanitized_inst cond i reg tc =
  let a = (+) (( * ) 4 i) 8 in
  wo_table
    (arm_assemble_all_cond
      ((coq_STR reg coq_SP (-4))::((coq_MOVW 14 reg ((land) a 0xffff))::(
      (coq_MOVT 14 reg ((land) ((lsr) a 16) 0xffff))::(sanitized_inst::(
      (coq_LDR reg coq_SP (-4))::[]))))) cond) tc

(** val rewrite_pc_sp_no_jump :
    arm_inst -> int -> int -> int -> int -> coq_TableCache -> coq_NewInst **)

let rewrite_pc_sp_no_jump sanitized_inst cond i reg reg2 tc =
  let a = (+) (( * ) 4 i) 8 in
  wo_table
    (arm_assemble_all_cond
      ((coq_STMDB2 coq_SP reg reg2)::((coq_MOV reg2 coq_SP)::((coq_MOVW 14
                                                                reg
                                                                ((land) a
                                                                  0xffff))::(
      (coq_MOVT 14 reg ((land) ((lsr) a 16) 0xffff))::(sanitized_inst::(
      (coq_LDMDB2 reg2 reg reg2)::[])))))) cond) tc

(** val rwl_pc : int -> int **)

let rwl_pc c =
  (+) (cd c) 15

(** val rwl_pc_sp : int -> int **)

let rwl_pc_sp c =
  (+) (cd c) 14

(** val rwl_pc_nj : int -> int **)

let rwl_pc_nj c =
  (+) (cd c) 5

(** val rwl_pc_sp_nj : int -> int **)

let rwl_pc_sp_nj c =
  (+) (cd c) 6

(** val canonical_z : int -> int -> int **)

let canonical_z w z =
  (-) ((land) ((+) z ((lsl) 1 ((-) w 1))) ((fun x -> ((lsl) 1 x)-1) w))
    ((lsl) 1 ((-) w 1))

(** val rewrite_b_bl :
    bool -> int -> int -> int -> int -> int list -> (int -> int) -> int ->
    coq_TableCache -> coq_NewInst **)

let rewrite_b_bl l lr cond imm24 i dis i2i' ai tc =
  let j =
    (land) ((+) ((+) i 2) (canonical_z 24 imm24))
      ((fun x -> ((lsl) 1 x)-1) 30)
  in
  let src = if l then (+) (i2i' i) 2 else i2i' i in
  let dst = if (fun _ _ -> true) j dis then i2i' j else ai in
  let m = if l then coq_MOVWT cond coq_LR lr else [] in
  (match wo_table
           (arm_assemble_all (List.append m ((coq_GOTO cond src dst)::[]))) tc with
   | Some z -> Some z
   | None ->
     (match wo_table
              (arm_assemble_all (List.append m ((coq_GOTO cond src ai)::[])))
              tc with
      | Some z -> Some z
      | None ->
        Some
          (((if l
             then 0xe1200070::(0xe1200070::(0xe1200070::[]))
             else 0xe1200070::[]),[]),tc)))

(** val rewrite_b :
    int -> int -> int -> int list -> (int -> int) -> int -> coq_TableCache ->
    coq_NewInst **)

let rewrite_b =
  rewrite_b_bl false 0

(** val rewrite_bl :
    int -> int -> int -> int -> int list -> (int -> int) -> int ->
    coq_TableCache -> coq_NewInst **)

let rewrite_bl =
  rewrite_b_bl true

(** val rewrite_mov_lr_pc :
    int -> int -> (int -> int) -> coq_TableCache -> coq_NewInst **)

let rewrite_mov_lr_pc cond i i2i' tc =
  let pc' = ( * ) 4 (i2i' ((+) i 2)) in
  wo_table
    (arm_assemble_all
      ((coq_MOVW cond coq_LR ((land) pc' 0xffff))::((coq_MOVT cond coq_LR
                                                      ((land) ((lsr) pc' 16)
                                                        0xffff))::[]))) tc

(** val _unused_reg : int -> int -> int -> int -> int **)

let _unused_reg base r0 r1 r2 =
  if if if (=) r0 base then true else (=) r1 base then true else (=) r2 base
  then if if if (=) r0 ((+) base 1) then true else (=) r1 ((+) base 1)
          then true
          else (=) r2 ((+) base 1)
       then if if if (=) r0 ((+) base 2) then true else (=) r1 ((+) base 2)
               then true
               else (=) r2 ((+) base 2)
            then (+) base 3
            else (+) base 2
       else (+) base 1
  else base

(** val unused_reg : int -> int -> int -> int **)

let unused_reg =
  _unused_reg 0

(** val unused_reg_high : int -> int -> int -> int **)

let unused_reg_high =
  _unused_reg 4

(** val goto_abort : int -> int -> coq_TableCache -> coq_NewInst **)

let goto_abort i' ai tc =
  match arm_assemble (coq_GOTO 14 i' ai) with
  | Some z -> Some (((z::[]),[]),tc)
  | None -> Some (((0xe1200070::[]),[]),tc)

(** val rewrite_inst_len : int -> int -> int -> int -> int **)

let rewrite_inst_len i bi txtlen z =
  let decoded = arm_decode z in
  (match decoded with
   | ARM_data_r (op, cond, _, rn, rd, _, _, rm) ->
     if (=) rd coq_PC
     then rwl_pc cond
     else if if (=) rn coq_PC then true else (=) rm coq_PC
          then if match op with
                  | ARM_MOV -> (=) rd coq_LR
                  | _ -> false
               then 2
               else if (=) rd coq_SP
                    then rwl_pc_sp_nj cond
                    else rwl_pc_nj cond
          else 1
   | ARM_data_i (_, cond, _, rn, rd, _) ->
     if (=) rd coq_PC
     then rwl_pc cond
     else if (=) rn coq_PC
          then if (=) rd coq_SP then rwl_pc_sp_nj cond else rwl_pc_nj cond
          else 1
   | ARM_BX (cond, reg) ->
     if if (<) reg 0 then true else (>=) reg coq_PC then 1 else rwl_bx cond
   | ARM_BLX_r (cond, reg) ->
     if if (<) reg 0 then true else (>=) reg coq_PC then 1 else rwl_blx cond
   | ARM_extra_ls_i (op, cond, _, _, _, rn, rt, _, _) ->
     if (=) rn coq_PC
     then if match op with
             | ARM_STRH -> false
             | ARM_STRD -> false
             | _ -> (=) rt coq_SP
          then rwl_pc_sp_nj cond
          else rwl_pc_nj cond
     else 1
   | ARM_extra_ls_r (op, cond, _, _, _, rn, rt, _) ->
     if (=) rn coq_PC
     then if match op with
             | ARM_STRH -> false
             | ARM_STRD -> false
             | _ -> (=) rt coq_SP
          then rwl_pc_sp_nj cond
          else rwl_pc_nj cond
     else 1
   | ARM_ls_i (op, cond, p, u, w, rn, rt, imm12) ->
     (match op with
      | ARM_LDR ->
        if (=) rt coq_PC
        then if if (=) rn coq_SP
                then if (=) p 0 then true else (=) w 1
                else false
             then rwl_pc_sp cond
             else rwl_pc cond
        else if (=) rn coq_PC
             then let loadedi =
                    (land)
                      (if (=) u 1
                       then (+) ((+) i 2) ((lsr) imm12 2)
                       else (-) ((+) i 2) ((lsr) imm12 2))
                      ((fun x -> ((lsl) 1 x)-1) 30)
                  in
                  let listi = (-) loadedi bi in
                  if (=) ((land) 3 imm12) 0
                  then if (>=) listi 0
                       then if (<) listi txtlen
                            then 2
                            else if (=) rt coq_SP
                                 then rwl_pc_sp_nj cond
                                 else rwl_pc_nj cond
                       else if (=) rt coq_SP
                            then rwl_pc_sp_nj cond
                            else rwl_pc_nj cond
                  else if (=) rt coq_SP
                       then rwl_pc_sp_nj cond
                       else rwl_pc_nj cond
             else 1
      | _ -> 1)
   | ARM_ls_r (op, cond, p, _, w, rn, rt, _, _, rm) ->
     (match op with
      | ARM_LDR ->
        if (=) rt coq_PC
        then if if (=) rn coq_SP
                then if (=) p 0 then true else (=) w 1
                else false
             then rwl_pc_sp cond
             else rwl_pc cond
        else if if (=) rn coq_PC then true else (=) rm coq_PC
             then if (=) rt coq_SP then rwl_pc_sp_nj cond else rwl_pc_nj cond
             else 1
      | _ -> 1)
   | ARM_lsm (op, cond, _, rn, register_list) ->
     if if if (<) register_list 0 then true else (<) rn 0
        then true
        else (>=) rn 15
     then 1
     else if (=) (bitb register_list 15) 0
          then 1
          else (match op with
                | ARM_STMDA -> 1
                | ARM_STMDB -> 1
                | ARM_STMIA -> 1
                | ARM_STMIB -> 1
                | _ -> rwl_ldm cond)
   | ARM_BL (_, _) -> 3
   | ARM_vls (_, _, cond, _, _, rn, _, _) ->
     if (=) rn coq_PC then rwl_pc_nj cond else 1
   | _ -> 1)

(** val rewrite_inst :
    coq_TableCache -> (int -> int) -> int -> int list -> int -> int -> int ->
    int -> int list -> (int -> bool) -> coq_NewInst **)

let rewrite_inst tc i2i' z dis i ti ai bi txt use_lr' =
  let unchanged = Some (((z::[]),[]),tc) in
  let abort = goto_abort (i2i' i) ai tc in
  let decoded = arm_decode z in
  let lr = if use_lr' i then ( * ) 4 (i2i' ((+) i 1)) else ( * ) 4 ((+) i 1)
  in
  if (not) ((fun _ _ -> true) ((+) i 1) dis)
  then None
  else (match decoded with
        | ARM_UNDEFINED -> abort
        | ARM_UNPREDICTABLE -> abort
        | ARM_data_r (op, cond, s, rn, rd, imm5, type0, rm) ->
          let reg = unused_reg rn rd rm in
          let reg2 = unused_reg_high rn rd rm in
          let rn' = if (=) rn coq_PC then reg else rn in
          let rd' = if (=) rd coq_PC then reg else rd in
          let rm' = if (=) rm coq_PC then reg else rm in
          let sanitized_inst = ARM_data_r (op, 14, s, rn', rd', imm5, type0,
            rm')
          in
          if (=) rd coq_PC
          then rewrite_pc sanitized_inst reg tc dis i2i' cond i ti ai
          else if if (=) rn coq_PC then true else (=) rm coq_PC
               then if match op with
                       | ARM_MOV -> (=) rd coq_LR
                       | _ -> false
                    then rewrite_mov_lr_pc cond i i2i' tc
                    else if (=) rd coq_SP
                         then rewrite_pc_sp_no_jump sanitized_inst cond i reg
                                reg2 tc
                         else rewrite_pc_no_jump sanitized_inst cond i reg tc
               else unchanged
        | ARM_data_i (op, cond, s, rn, rd, imm12) ->
          let reg = unused_reg rn rd 0 in
          let reg2 = unused_reg_high rn rd 0 in
          let rn' = if (=) rn coq_PC then reg else rn in
          let rd' = if (=) rd coq_PC then reg else rd in
          let sanitized_inst = ARM_data_i (op, 14, s, rn', rd', imm12) in
          if (=) rd coq_PC
          then rewrite_pc sanitized_inst reg tc dis i2i' cond i ti ai
          else if (=) rn coq_PC
               then if (=) rd coq_SP
                    then rewrite_pc_sp_no_jump sanitized_inst cond i reg reg2
                           tc
                    else rewrite_pc_no_jump sanitized_inst cond i reg tc
               else unchanged
        | ARM_BX (cond, reg) ->
          if if (<) reg 0 then true else (>=) reg coq_PC
          then rewrite_b cond 0 i dis i2i' ai tc
          else rewrite_bx reg tc dis i2i' cond i ti ai
        | ARM_BLX_r (cond, reg) ->
          if if (<) reg 0 then true else (>=) reg coq_PC
          then abort
          else rewrite_blx lr reg tc dis i2i' cond i ti ai
        | ARM_BXJ (_, _) -> abort
        | ARM_BKPT (_, _, _) -> abort
        | ARM_extra_ls_i (op, cond, p, u, w, rn, rt, imm4H, imm4L) ->
          let reg = if (=) rt 0 then 1 else 0 in
          let reg2 = if (=) rt 2 then 3 else 2 in
          let sanitized_inst = ARM_extra_ls_i (op, cond, p, u, w, reg, rt,
            imm4H, imm4L)
          in
          if (=) rn coq_PC
          then if match op with
                  | ARM_STRH -> false
                  | ARM_STRD -> false
                  | _ -> (=) rt coq_SP
               then rewrite_pc_sp_no_jump sanitized_inst cond i reg reg2 tc
               else rewrite_pc_no_jump sanitized_inst cond i reg tc
          else unchanged
        | ARM_extra_ls_r (op, cond, p, u, w, rn, rt, rm) ->
          let reg = if (=) rt 0 then 1 else 0 in
          let reg2 = if (=) rt 2 then 3 else 2 in
          let sanitized_inst = ARM_extra_ls_r (op, cond, p, u, w, reg, rt, rm)
          in
          if (=) rn coq_PC
          then if match op with
                  | ARM_STRH -> false
                  | ARM_STRD -> false
                  | _ -> (=) rt coq_SP
               then rewrite_pc_sp_no_jump sanitized_inst cond i reg reg2 tc
               else rewrite_pc_no_jump sanitized_inst cond i reg tc
          else unchanged
        | ARM_ls_i (op, cond, p, u, w, rn, rt, imm12) ->
          (match op with
           | ARM_LDR ->
             let reg = unused_reg rn rt 0 in
             let reg2 = unused_reg_high rn rt 0 in
             let rn' = if (=) rn coq_PC then reg else rn in
             let rt' = if (=) rt coq_PC then reg else rt in
             let sanitized_inst = ARM_ls_i (ARM_LDR, cond, p, u, w, rn', rt',
               imm12)
             in
             if (=) rt coq_PC
             then if if (=) rn coq_SP
                     then if (=) p 0 then true else (=) w 1
                     else false
                  then rewrite_pc_sp sanitized_inst reg reg2 tc dis i2i' cond
                         i ti ai
                  else rewrite_pc sanitized_inst reg tc dis i2i' cond i ti ai
             else if (=) rn coq_PC
                  then let loadedi =
                         (land)
                           (if (=) u 1
                            then (+) ((+) i 2) ((lsr) imm12 2)
                            else (-) ((+) i 2) ((lsr) imm12 2))
                           ((fun x -> ((lsl) 1 x)-1) 30)
                       in
                       let listi = (-) loadedi bi in
                       if (=) ((land) 3 imm12) 0
                       then if (>=) listi 0
                            then (match (fun a i -> if i < Array.length a then Some (Array.get a i) else None)
                                          txt ( listi) with
                                  | Some lv ->
                                    wo_table
                                      (arm_assemble_all
                                        ((coq_MOVW cond rt ((land) lv 0xffff))::(
                                        (coq_MOVT cond rt
                                          ((land) ((lsr) lv 16) 0xffff))::[])))
                                      tc
                                  | None ->
                                    if (=) rt coq_SP
                                    then rewrite_pc_sp_no_jump sanitized_inst
                                           cond i reg reg2 tc
                                    else rewrite_pc_no_jump sanitized_inst
                                           cond i reg tc)
                            else if (=) rt coq_SP
                                 then rewrite_pc_sp_no_jump sanitized_inst
                                        cond i reg reg2 tc
                                 else rewrite_pc_no_jump sanitized_inst cond
                                        i reg tc
                       else if (=) rt coq_SP
                            then rewrite_pc_sp_no_jump sanitized_inst cond i
                                   reg reg2 tc
                            else rewrite_pc_no_jump sanitized_inst cond i reg
                                   tc
                  else unchanged
           | _ -> unchanged)
        | ARM_ls_r (op, cond, p, u, w, rn, rt, imm5, type0, rm) ->
          (match op with
           | ARM_LDR ->
             let reg = unused_reg rn rt rm in
             let reg2 = unused_reg_high rn rt rm in
             let rn' = if (=) rn coq_PC then reg else rn in
             let rt' = if (=) rt coq_PC then reg else rt in
             let rm' = if (=) rm coq_PC then reg else rm in
             let sanitized_inst = ARM_ls_r (ARM_LDR, cond, p, u, w, rn', rt',
               imm5, type0, rm')
             in
             if (=) rt coq_PC
             then if if (=) rn coq_SP
                     then if (=) p 0 then true else (=) w 1
                     else false
                  then rewrite_pc_sp sanitized_inst reg reg2 tc dis i2i' cond
                         i ti ai
                  else rewrite_pc sanitized_inst reg tc dis i2i' cond i ti ai
             else if if (=) rn coq_PC then true else (=) rm coq_PC
                  then if (=) rt coq_SP
                       then rewrite_pc_sp_no_jump sanitized_inst cond i reg
                              reg2 tc
                       else rewrite_pc_no_jump sanitized_inst cond i reg tc
                  else unchanged
           | _ -> unchanged)
        | ARM_bfx (_, _, _, _, _, _) -> abort
        | ARM_lsm (op, cond, _, rn, register_list) ->
          if if if (<) register_list 0 then true else (<) rn 0
             then true
             else (>=) rn 15
          then abort
          else if (=) (bitb register_list 15) 0
               then unchanged
               else (match op with
                     | ARM_STMDA -> unchanged
                     | ARM_STMDB -> unchanged
                     | ARM_STMIA -> unchanged
                     | ARM_STMIB -> unchanged
                     | _ ->
                       let reg = if (=) rn 0 then 1 else 0 in
                       rewrite_ldm_pc op rn register_list reg decoded tc dis
                         i2i' cond i ti ai)
        | ARM_B (cond, imm24) -> rewrite_b cond imm24 i dis i2i' ai tc
        | ARM_BL (cond, imm24) -> rewrite_bl lr cond imm24 i dis i2i' ai tc
        | ARM_BLX_i (_, _) -> abort
        | ARM_vls (is_load, is_single, cond, u, d, rn, vd, imm8) ->
          if (=) rn coq_PC
          then let sanitized_inst = ARM_vls (is_load, is_single, cond, u, d,
                 0, vd, imm8)
               in
               rewrite_pc_no_jump sanitized_inst cond i 0 tc
          else unchanged
        | _ -> unchanged)

(** val _rewrite :
    int list -> coq_TableCache -> (int -> int list) -> (int -> int) -> int ->
    int -> int -> int -> int list -> (int -> bool) -> (int list list * int
    list list) option **)

let rec _rewrite zs tc pol i2i' i ti ai bi txt use_lr' =
  if if if (>=) i ((lsl) 1 30)
        then true
        else (>=) (i2i' i) ((-) ((lsl) 1 30) 1)
     then true
     else (>=) ti ((lsl) 1 30)
  then None
  else (match zs with
        | [] -> Some (((0xe1200070::[])::[]),[])
        | z::zs0 ->
          (match rewrite_inst tc i2i' z (pol i) i ti ai bi txt use_lr' with
           | Some p ->
             let p0,tc' = p in
             let z',table = p0 in
             let ti' = (+) ti ( (List.length table)) in
             (match _rewrite zs0 tc' pol i2i' ((+) i 1) ti' ai bi txt use_lr' with
              | Some p1 ->
                let z_t,table_t = p1 in Some ((z'::z_t),(table::table_t))
              | None -> None)
           | None -> None))

(** val make_i's : int list -> int -> int list **)

let make_i's lens i' =
  List.rev
    (snd
      ((fun f l a -> List.fold_left f a l) (fun a b ->
        let sum = (+) (fst a) b in sum,(((+) i' (fst a))::(snd a))) lens
        (0,[])))

(** val make_i2i' : int -> int -> int -> int list -> int -> int **)

let make_i2i' bi bi' ai lens =
  let i's = make_i's lens bi' in
  let ie = (+) bi ( (List.length lens)) in
  let ie' = (+) bi' ((fun f l a -> List.fold_left f a l) (+) lens 0) in
  let arr = Array.of_list i's in
  (fun x ->
  if if (<) x bi then true else (>=) x ie
  then if if (<) x bi' then true else (>=) x ie' then x else ai
  else Array.get arr ((-) x bi))

(** val cfi_rw :
    (int -> int list) -> int list -> int -> int -> int -> int -> (int ->
    bool) -> (int list list * int list list) option **)

let cfi_rw pol code bi bi' ti ai use_lr' =
  let tc = fun _ -> None in
  let irm_lens =
    List.mapi (fun i -> rewrite_inst_len ((+) bi i) bi ( (List.length code)))
      code
  in
  let i2i' = make_i2i' bi bi' ai irm_lens in
  _rewrite code tc pol i2i' bi ti ai bi (Array.of_list code) use_lr'
