(*
  PIL notations for simplifying semantics writing.
 *)

Require Import Picinae_armv8_pcode.
Require Import List String Ascii NArith Bool.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope N_scope.

Module Notation.
Declare Custom Entry PIL.

(* ---------- entry point ---------- *)
Notation "<{ e }>" := (e) (e custom PIL at level 99).

(* ================= expressions ================= *)

(* Let any plain Gallina atom (identifier, literal, etc.) count as a PIL term *)
Notation "x" := x (in custom PIL at level 0, x constr at level 0).

(* Parentheses for grouping. *)
Notation "( x )" := x (in custom PIL at level 0, x at level 99).

(* Braces for escaping *)
Notation "{ x }" := x (in custom PIL at level 0, x constr at level 200).

(* word literal: 42#32 *)
Notation "n '#' w" := (Word n w)
  (in custom PIL at level 2,  w at level 99, no associativity).
Definition w32 := <{ 0 # 32 }>.

Notation "'load' '[' addr ',' en ',' w ']'" := (Load (Var V_MEM64) addr en w)
  (in custom PIL at level 2, addr at level 99, en at level 0, w at level 0).

Definition f := <{ load [ w32 , LittleE , 4 ] }>.

Notation "'store' '[' addr ',' val ',' en ',' w ']'" := (Move V_MEM64 (Store (Var V_MEM64) addr val en w))
  (in custom PIL at level 2, addr at level 99, val at level 99, en at level 0, w at level 0).


(* --- binary ops: rename OP_PLUS/OP_MINUS/OP_LSHIFT/OP_RSHIFT to match your binop_typ --- *)
Notation "x + y"  := (BinOp OP_PLUS   x y) (in custom PIL at level 50, left associativity).
Notation "x - y"  := (BinOp OP_MINUS  x y) (in custom PIL at level 50, left associativity).

(* --- multiplicative: bind tighter than +/- --- *)
Notation "x * y"  := (BinOp OP_TIMES  x y) (in custom PIL at level 40, left associativity).
Notation "x / y"  := (BinOp OP_DIVIDE x y) (in custom PIL at level 40, left associativity).
Notation "x % y"  := (BinOp OP_MOD    x y) (in custom PIL at level 40, left associativity).

(* --- shifts  --- *)
Notation "x << y" := (BinOp OP_LSHIFT x y) (in custom PIL at level 55, left associativity).
Notation "x >> y" := (BinOp OP_RSHIFT x y) (in custom PIL at level 55, left associativity).
Notation "x >>a y" := (BinOp OP_ARSHIFT x y) (in custom PIL at level 55, left associativity).

(* --- bitwise --- *)
Notation "! x"    := (UnOp  OP_NOT x)   (in custom PIL at level 60).
Notation "x & y"  := (BinOp OP_AND x y) (in custom PIL at level 65, left associativity).
Notation "x ^ y"  := (BinOp OP_XOR x y) (in custom PIL at level 68, left associativity).
Notation "x | y"  := (BinOp OP_OR  x y) (in custom PIL at level 70, left associativity).

(* --- comparisons: loosest, don't chain --- *)
Notation "x = y"   := (BinOp OP_EQ  x y) (in custom PIL at level 75, no associativity).
Notation "x <> y"  := (BinOp OP_NEQ x y) (in custom PIL at level 75, no associativity).
Notation "x < y"   := (BinOp OP_LT  x y) (in custom PIL at level 75, no associativity).
Notation "x <= y"  := (BinOp OP_LE  x y) (in custom PIL at level 75, no associativity).
Notation "x 's<' y"  := (BinOp OP_SLT x y) (in custom PIL at level 75, no associativity).
Notation "x 's<=' y" := (BinOp OP_SLE x y) (in custom PIL at level 75, no associativity).


Notation "'ucast' w e" := (Cast CAST_UNSIGNED w e) (in custom PIL at level 0, w at level 0, e at level 99).
Notation "'scast' w e" := (Cast CAST_SIGNED   w e) (in custom PIL at level 0, w at level 0, e at level 99).
Notation "'hcast' w e" := (Cast CAST_HIGH     w e) (in custom PIL at level 0, w at level 0, e at level 99).
Notation "'lcast' w e" := (Cast CAST_LOW      w e) (in custom PIL at level 0, w at level 0, e at level 99).


Notation "'unknown' w" := (Unknown w) (in custom PIL at level 0, w at level 0).

Notation "'ite' e1 e2 e3" := (Ite e1 e2 e3)
  (in custom PIL at level 0, e2 at level 99, e3 at level 99).

Notation "e [ hi ':' lo ]" := (Extract hi lo e)
  (in custom PIL at level 2, hi at level 0, lo at level 0).

Notation "e [ n1 ]" := (Extract n1 n1 e)
  (in custom PIL at level 2, n1 at level 0).

Notation "x '++' y" := (Concat x y) (in custom PIL at level 60, right associativity).

(* ================= statements ================= *)

Notation "'nop'"    := Nop (in custom PIL at level 0).

Notation "v := e" := (Move v e)
  (in custom PIL at level 0,  e at level 85, no associativity).

Notation "'let' v ':=' e1 'in' e2" := (Let v e1 e2)
  (in custom PIL at level 0, v constr at level 0, e1 at level 99, e2 at level 99).

Notation "'vSP'" := (100%N).

Notation "'jmp' e"  := (Jmp e) (in custom PIL at level 0, e at level 99).
Notation "'exn' i"  := (Exn i) (in custom PIL at level 0, i at level 0).
Notation "q1 ; q2"  := (Seq q1 q2) (in custom PIL at level 90, right associativity).
Notation "'if' e 'then' q1 'else' q2 'end'" := (If e q1 q2)
  (in custom PIL at level 89, e at level 199, q1 at level 99, q2 at level 99).
Notation "'rep' e 'do' q 'end'" := (Rep e q)
  (in custom PIL at level 89, e at level 99, q at level 99).
End Notation.
