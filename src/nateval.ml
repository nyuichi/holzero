(* ========================================================================== *)
(* NATURAL NUMBER EVALUATION (HOL Zero)                                       *)
(* - Conversions for evaluating natural numeral arithmetic                    *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2010-2015                            *)
(* ========================================================================== *)


module NatEval : NatEval_sig = struct


(* This module defines conversions for evaluating arithmetic operations on    *)
(* natual number numerals.  Because large proofs may involve heavy numeric    *)
(* computation, special consideration is given to the efficieny of these      *)
(* functions.                                                                 *)

(* Throughout the module, the HOL variables "l", "m" and "n" are used for     *)
(* natural numbers that are free in the pre-computed evaluation lemmas.  Free *)
(* vars are used in these lemmas because the rule for instantiating free vars *)
(* is much faster than the rule for specialising universal quantifiers.       *)


open Equal;;
open EqCong;;
open Bool;;
open BoolAlg;;
open BoolClass;;

open Nat;;
open NatNumrl;;
open NatArith;;
open NatRel;;


(* HOL variables *)

let l = `l:nat`;;
let m = `m:nat`;;
let n = `n:nat`;;
let z = `z:nat`;;



(* ** BIT0/1 EXTRA SUPPORT ** *)

(* This section defines a destructor utility for breaking down numerals into  *)
(* a dedicated datatype, and alternative definitions of "BIT0" and "BIT1".    *)


(* Destructed numeral datatype *)

(* This enables ML 'match' clauses to be used in the evaluation conversions,  *)
(* for a neater implementation.                                               *)

type destructed_bit =
    Bit0 of term
  | Bit1 of term
  | Zero
  | One;;


(* dest_bit - destructs untagged numerals into 'Bit0', 'Bit1' or 'Zero'       *)

let dest_bit tm =
  try
    let (f,tm0) = try0 dest_comb tm     LocalFail in
    let x = try0 const_name f    LocalFail in
    match x with
      "BIT0" -> Bit0 tm0
    | "BIT1" -> Bit1 tm0
    | _      -> hol_fail ("dest_bit", "Not an untagged numeral")
  with LocalFail ->
    if (tm = zero_tm0)
      then Zero
      else hol_fail ("dest_bit", "Not an untagged numeral");;


(* dest_bit1 - destructs untagged numerals into 'Bit0', 'Bit1', 'One', 'Zero' *)

let dest_bit1 tm =
  let btm = dest_bit tm in
  match btm with
    (Bit1 tm0) -> if (tm0 = zero_tm0) then One
                                      else btm
  | _          -> btm;;


(* bit0_adddef_thm                                                            *)
(*                                                                            *)
(*    |- !n. BIT0 n = n + n                                                   *)

let bit0_adddef_thm =
  (* |- !n. BIT0 n = n + n                           *)
  mp_rule
    (bspec_rule `\n. BIT0 n = n + n` nat_induction_thm)
    (conj_rule
      (* |- BIT0 0 = 0 + 0                                       *)
      (eq_trans_rule (numeralise_mono_rule (conjunct1_rule bit0_def))
                     (eq_sym_rule (spec_rule `0` add_id_thm)) )
      (* |- !n. BIT0 n = n + n ==> BIT0 (SUC n) = SUC n + SUC n  *)
      (gen_rule n
        (disch_rule `BIT0 n = n + n`
          (list_eq_trans_rule
             [ (* |- BIT0 (SUC n) = SUC (SUC (BIT0 n))               *)
               spec_rule n (conjunct2_rule bit0_def);
               (* BIT0 n = n + n                                     *)
               (*   |- SUC (SUC (BIT0 n)) = SUC (SUC (n + n))        *)
               mk_comb2_rule `SUC`
                (mk_comb2_rule `SUC`
                  (assume_rule `BIT0 n = n + n`) );
               (* |- SUC (SUC (n + n)) = SUC n + SUC n               *)
               eq_sym_rule
                (eq_trans_rule
                  (list_spec_rule [n;`SUC n`] add_dist_left_suc_thm)
                  (mk_comb2_rule `SUC`
                    (list_spec_rule [n;n] add_dist_right_suc_thm) )) ]))));;


(* bit1_adddef_thm                                                            *)
(*                                                                            *)
(*    |- !n. BIT1 n = SUC (n + n)                                             *)

let bit1_adddef_thm =
  gen_rule n
   (eq_trans_rule
     (* |- BIT1 n = SUC (BIT0 n)           *)
     (spec_rule n bit1_def)
     (* |- SUC (BIT0 n) = SUC (n + n)      *)
     (mk_comb2_rule `SUC` (spec_rule n bit0_adddef_thm)) );;


(* bit0_multdef_thm                                                           *)
(*                                                                            *)
(*    |- !n. BIT0 n = 2 * n                                                   *)

let bit0_multdef_thm =
  gen_rule n
    (eq_trans_rule
      (* |- BIT0 n = n + n                  *)
      (spec_rule n bit0_adddef_thm)
      (* |- n + n = 2 * n                   *)
      (eq_sym_rule (spec_rule n twice_thm)) );;


(* bit1_multdef_thm                                                           *)
(*                                                                            *)
(*    |- !n. BIT1 n = SUC (2 * n)                                             *)

let bit1_multdef_thm =
  gen_rule n
    (eq_trans_rule
      (* |- BIT1 n = SUC (n + n)        *)
      (spec_rule n bit1_adddef_thm)
      (* |- ...    = SUC (2 * n)        *)
      (eq_sym_rule (mk_comb2_rule `SUC` (spec_rule n twice_thm))) );;


(* bit1_multadddef_thm                                                        *)
(*                                                                            *)
(*    |- !n. BIT1 n = 2 * n + 1                                               *)

let bit1_multadddef_thm =
  gen_rule n
    (eq_trans_rule
      (* |- BIT1 n = SUC (2 * n)        *)
      (spec_rule n bit1_multdef_thm)
      (* |- ...    = 2 * n + 1          *)
      (spec_rule `2*n` suc_add_thm) );;



(* ** SUCCESSOR EVALUATION ** *)


(* Evaluation lemmas *)

let suc_bit0_lemma =        (* |- SUC (BIT0 n) = BIT1 n           *)
  eq_trans_rule
    (* |- SUC (BIT0 n) = SUC (n + n)             *)
    (mk_comb2_rule `SUC` (spec_rule n bit0_adddef_thm))
    (* |- SUC (n + n) = BIT1 n                   *)
    (eq_sym_rule (spec_rule n bit1_adddef_thm));;

let suc_bit1_lemma =        (* |- SUC (BIT1 n) = BIT0 (SUC n)     *)
  list_eq_trans_rule
    [ (* |- SUC (BIT1 n) = SUC (SUC (n + n))     *)
      mk_comb2_rule `SUC` (spec_rule n bit1_adddef_thm);
      (* |- ...          = SUC n + SUC n         *)
      eq_sym_rule
        (eq_trans_rule
          (list_spec_rule [`SUC n`;n] add_dist_right_suc_thm)
          (mk_comb2_rule `SUC` (list_spec_rule [n;n] add_dist_left_suc_thm)));
      (* |- ...          = BIT0 (SUC n)          *)
      eq_sym_rule (spec_rule `SUC n` bit0_adddef_thm) ];;


(* eval_suc_conv : term -> thm                                                *)
(*                                                                            *)
(* This is the evaluation conversion for numeral successor.  It takes a term  *)
(* of the form `SUC n`, where "n" is a natural number numeral, and returns a  *)
(* theorem stating that this equals its numeral value, under no assumptions.  *)
(*                                                                            *)
(*       `SUC n`                                                              *)
(*    ------------                                                            *)
(*    |- SUC n = z                                                            *)

let rec eval_suc_conv0 tm0 =
  match (dest_bit1 tm0) with
    Bit0 tm00
       -> (*  SUC (BIT0 n)  -->  BIT1 n               *)
          inst_rule [(n,tm00)] suc_bit0_lemma
  | Bit1 tm00
       -> (*  SUC (BIT1 n)  -->  BIT0 (SUC n)         *)
          eq_trans_rule (inst_rule [(n,tm00)] suc_bit1_lemma)
                        (mk_comb2_rule bit0_fn (eval_suc_conv0 tm00))
  | Zero
       -> (*  SUC ZERO  -->  BIT1 ZERO                *)
          suc_zero_thm0
  | One
       -> (*  SUC (BIT1 ZERO)  -->  BIT0 (BIT1 ZERO)  *)
          suc_one_thm0;;

let eval_suc_conv tm =
  let func = "eval_suc_conv" in
  let tm0 = try1 dest_suc tm      (func, "Not a 'SUC' expression") in
  let () = assert1 (is_nat tm0)   (func, "'SUC' arg is not a numeral") in
  let tm00 = dest_numeral_tag tm0 in
  numeralise_mono_rule (eval_suc_conv0 tm00);;



(* ** PREDECESSOR EVALUATION ** *)


(* Evaluation lemma *)

let pre_suc_lemma =       (* |- SUC z = n ==> PRE n = z      *)
  disch_rule `SUC z = n`
    (subs_rule [assume_rule `SUC z = n`] (spec_rule z pre_suc_thm));;


(* eval_pre_conv : term -> thm                                                *)
(*                                                                            *)
(* This is the evaluation conversion for numeral predecessor.  It takes a     *)
(* term of the form `PRE n`, where "n" is a natural number numeral, and       *)
(* returns a theorem stating that this equals its numeral value, under no     *)
(* assumptions.                                                               *)
(*                                                                            *)
(*       `PRE n`                                                              *)
(*    ------------                                                            *)
(*    |- PRE n = z                                                            *)

(* For the non-trivial case, this is implemented by working out the result    *)
(* `z` in ML and then working backwards from evaluating `SUC z` in HOL.       *)

let pre_zero_thm0 = subs_rule [numeral_zero_thm] pre_zero_thm;;

let eval_pre_conv0 tm0 =
  let i = dest_nat_big_int0 tm0 in
  if (eq_big_int i big_int_0)
    then (*  PRE 0  -->  0                                    *)
         pre_zero_thm0
    else (*  [ SUC z = n ]  PRE n  -->  z                     *)
         let tm1 = mk_nat_big_int0 (pred_big_int i) in
         mp_rule
           (inst_rule [(n,tm0);(z,tm1)] pre_suc_lemma)
           (eval_suc_conv0 tm1);;

let eval_pre_conv tm =
  let func = "eval_pre_conv" in
  let tm0 = try1 dest_pre tm      (func, "Not a 'PRE' expression") in
  let () = assert1 (is_nat tm0)   (func, "'PRE' arg is not a numeral") in
  let tm00 = dest_numeral_tag tm0 in
  numeralise_mono_rule (eval_pre_conv0 tm00);;



(* ** ADDITION EVALUATION ** *)


(* mmnn_add_lemma                                                             *)
(*                                                                            *)
(*    |- (m + m) + (n + n) = (m + n) + (m + n)                                *)

let mmnn_add_lemma =
  list_spec_rule [m;m;n;n] (get_lemma "add_switch_lemma");;


(* Evaluation lemmas *)

let add_id_thm0 = subs_rule [numeral_zero_thm] add_id_thm;;

let zero_add_lemma =        (* |- ZERO + n = n                           *)
  eq_trans_rule
    (list_spec_rule [`ZERO`;n] add_comm_thm)
    (spec_rule n add_id_thm0);;

let add_zero_lemma =        (* |- n + ZERO = n                           *)
  spec_rule n add_id_thm0;;

let bit0_add_bit0_lemma =   (* |- BIT0 m + BIT0 n = BIT0 (m + n)         *)
  list_eq_trans_rule
    [ (* |- BIT0 m + BIT0 n = (m + m) + (n + n)      *)
      mk_bin_rule `$+` (spec_rule m bit0_adddef_thm)
                       (spec_rule n bit0_adddef_thm);
      (* |- ...             = (m + n) + (m + n)      *)
      mmnn_add_lemma;
      (* |- ...             = BIT0 (m + n)           *)
      eq_sym_rule (spec_rule `m+n` bit0_adddef_thm) ];;

let bit0_add_bit1_lemma =   (* |- BIT0 m + BIT1 n = BIT1 (m + n)         *)
  list_eq_trans_rule
    [ (* |- BIT0 m + BIT1 n = (m + m) + SUC (n + n)   *)
      mk_bin_rule `$+` (spec_rule m bit0_adddef_thm)
                       (spec_rule n bit1_adddef_thm);
      (* |- ...             = SUC ((m+m) + (n+n))     *)
      list_spec_rule [`m+m`;`n+n`] add_dist_right_suc_thm;
      (* |- ...             = SUC ((m+n) + (m+n))     *)
      mk_comb2_rule `SUC` mmnn_add_lemma;
      (* |- ...             = BIT1 (m+n)              *)
      eq_sym_rule (spec_rule `m+n` bit1_adddef_thm) ];;

let bit1_add_bit0_lemma =   (* |- BIT1 m + BIT0 n = BIT1 (m + n)         *)
  list_eq_trans_rule
    [ (* |- BIT1 m + BIT0 n = SUC (m + m) + (n + n)   *)
      mk_bin_rule `$+` (spec_rule m bit1_adddef_thm)
                       (spec_rule n bit0_adddef_thm);
      (* |- ...             = SUC ((m+m) + (n+n))     *)
      list_spec_rule [`m+m`;`n+n`] add_dist_left_suc_thm;
      (* |- ...             = SUC ((m+n) + (m+n))     *)
      mk_comb2_rule `SUC` mmnn_add_lemma;
      (* |- ...             = BIT1 (m+n)              *)
      eq_sym_rule (spec_rule `m+n` bit1_adddef_thm) ];;

let bit1_add_bit1_lemma =   (* |- BIT1 m + BIT1 n = BIT0 (SUC (m + n))   *)
  list_eq_trans_rule
    [ (* |- BIT1 m + BIT1 n = SUC (m + m) + SUC (n + n)        *)
      mk_bin_rule `$+` (spec_rule m bit1_adddef_thm)
                       (spec_rule n bit1_adddef_thm);
      (* |- ...             = SUC (SUC ((m + m) + (n + n)))    *)
      list_spec_rule [`m+m`;`SUC (n+n)`] add_dist_left_suc_thm;
      mk_comb2_rule `SUC`
        (list_spec_rule [`m+m`;`n+n`] add_dist_right_suc_thm);
      (* |- ...             = SUC (SUC ((m + n) + (m + n)))    *)
      mk_comb2_rule `SUC` (mk_comb2_rule `SUC` mmnn_add_lemma);
      (* |- ...             = SUC (m + n) + SUC (m + n)        *)
      eq_sym_rule
        (mk_comb2_rule `SUC`
                (list_spec_rule [`m+n`;`m+n`] add_dist_left_suc_thm));
      eq_sym_rule
        (list_spec_rule [`SUC (m+n)`;`m+n`] add_dist_right_suc_thm);
      (* |- ...             = BIT0 (SUC (m + n))               *)
      eq_sym_rule (spec_rule `SUC (m+n)` bit0_adddef_thm) ];;


(* eval_add_conv : term -> thm                                                *)
(*                                                                            *)
(* This is the evaluation conversion for numeral addition.  It takes a term   *)
(* of the form `m + n`, where "m" and "n" are both natural number numerals,   *)
(* and returns a theorem stating that this equals its numeral value, under no *)
(* assumptions.                                                               *)
(*                                                                            *)
(*       `m + n`                                                              *)
(*    ------------                                                            *)
(*    |- m + n = z                                                            *)

let rec eval_add_conv0 tm1 tm2 =
  match (dest_bit tm1, dest_bit tm2) with
    (Bit0 tm01, Bit0 tm02)
       -> (*  BIT0 m + BIT0 n  -->  BIT0 (m + n)         *)
          eq_trans_rule
            (inst_rule [(m,tm01);(n,tm02)] bit0_add_bit0_lemma)
            (mk_comb2_rule bit0_fn (eval_add_conv0 tm01 tm02))
  | (Bit0 tm01, Bit1 tm02)
       -> (*  BIT0 m + BIT1 n  -->  BIT1 (m + n)         *)
          eq_trans_rule
            (inst_rule [(m,tm01);(n,tm02)] bit0_add_bit1_lemma)
            (mk_comb2_rule bit1_fn (eval_add_conv0 tm01 tm02))
  | (Bit1 tm01, Bit0 tm02)
       -> (*  BIT1 m + BIT0 n  -->  BIT1 (m + n)         *)
          eq_trans_rule
            (inst_rule [(m,tm01);(n,tm02)] bit1_add_bit0_lemma)
            (mk_comb2_rule bit1_fn (eval_add_conv0 tm01 tm02))
  | (Bit1 tm01, Bit1 tm02)
       -> (*  BIT1 m + BIT1 n  -->  BIT1 (SUC (m + n))   *)
          let th00 = eval_add_conv0 tm01 tm02 in
          eq_trans_rule
            (inst_rule [(m,tm01);(n,tm02)] bit1_add_bit1_lemma)
            (mk_comb2_rule bit0_fn
              (eq_trans_rule (mk_comb2_rule suc_fn th00)
                             (eval_suc_conv0 (eqthm_rhs th00)) ))
  | (_, Zero)
       -> (*  n + ZERO  -->  n                           *)
          inst_rule [(n,tm1)] add_zero_lemma
  | (Zero, _)
       -> (*  ZERO + n  -->  n                           *)
          inst_rule [(n,tm2)] zero_add_lemma
  | _  -> internal_error "eval_add_conv0";;

let eval_add_conv tm =
  let func = "eval_add_conv" in
  let (tm1,tm2) = try1 dest_add tm    (func, "Not a '+' expression") in
  let () = assert1 (is_nat tm1)        (func, "'+' 1st arg is not a numeral") in
  let () = assert1 (is_nat tm2)        (func, "'+' 2nd arg is not a numeral") in
  let tm01 = dest_numeral_tag tm1 in
  let tm02 = dest_numeral_tag tm2 in
  numeralise_bin_rule (eval_add_conv0 tm01 tm02);;



(* ** MULTIPLICATION EVALUATION ** *)


(* Evaluation lemmas *)

let one_tm0 = `BIT1 ZERO`;;
let mult_zero_thm0 = subs_rule [numeral_zero_thm] mult_zero_thm;;
let mult_id_thm0 = subs_rule [numeral_one_thm] mult_id_thm;;

let zero_mult_lemma =      (* |- ZERO * n = ZERO               *)
  eq_trans_rule
    (list_spec_rule [zero_tm0;n] mult_comm_thm)
    (spec_rule n mult_zero_thm0);;

let mult_zero_lemma =      (* |- n * ZERO = ZERO               *)
  spec_rule n mult_zero_thm0;;

let one_mult_lemma =       (* |- 1 * n = n                     *)
  eq_trans_rule
    (list_spec_rule [one_tm0;n] mult_comm_thm)
    (spec_rule n mult_id_thm0);;

let mult_one_lemma =       (* |- n * 1 = n                     *)
  spec_rule n mult_id_thm0;;

let bit0_mult_lemma =      (* |- (BIT0 m) * n = BIT0 (m * n)   *)
  list_eq_trans_rule
     [ (* |- BIT0 m * n = (2 * m) * n          *)
       mk_bin1_rule `$*` (spec_rule m bit0_multdef_thm) n;
       (* |- ...        = 2 * (m * n)          *)
       eq_sym_rule (list_spec_rule [`2`;m;n] mult_assoc_thm);
       (* |- ...        = BIT0 (m * n)         *)
       eq_sym_rule (spec_rule `m * n` bit0_multdef_thm) ];;

let mult_bit0_lemma =      (* |- m * (BIT0 n) = BIT0 (m * n)   *)
  list_eq_trans_rule
     [ (* |- m * BIT0 n = m * (2 * n)          *)
       mk_bin2_rule `$*` m (spec_rule n bit0_multdef_thm);
       (* |- ...        = 2 * (m * n)          *)
       eq_sym_rule
         (list_spec_rule [`2`;m;n] (get_lemma "mult_left_flip_lemma"));
       (* |- ...        = BIT0 (m * n)         *)
       eq_sym_rule (spec_rule `m * n` bit0_multdef_thm) ];;

let bit1_mult_bit1_lemma =
                  (* |- (BIT1 m) * (BIT1 n) = BIT1 (BIT0 (m * n) + (m + n))  *)
  list_eq_trans_rule
    [ (* |- (BIT1 m) * (BIT1 n) = (2*m + 1) * (2*n + 1)              *)
      mk_bin_rule `$*` (spec_rule m bit1_multadddef_thm)
                       (spec_rule n bit1_multadddef_thm);
      (* |- ...                 = (2*m) * (2*n + 1) + 1 * (2*n + 1)  *)
      list_spec_rule [`2*m`;`1`;`2*n+1`] mult_dist_left_add_thm;
      (* |- ...                 = (2 * (m * (2*n + 1)) + 2 * n) + 1  *)
      (mk_bin_rule `$+`
        (eq_sym_rule (list_spec_rule [`2`;m;`2*n+1`] mult_assoc_thm))
        (eq_trans_rule (list_spec_rule [`1`;`2*n+1`] mult_comm_thm)
                       (spec_rule `2*n+1` mult_id_thm) ));
      list_spec_rule [`2*(m*(2*n+1))`;`2*n`;`1`] add_assoc_thm;
      (* |- ...                 = 2 * (m * (2*n + 1) + n) + 1        *)
      eq_sym_rule (mk_bin1_rule `$+`
          (list_spec_rule [`2`;`m*(2*n+1)`;n] mult_dist_right_add_thm) `1`);
      (* |- ...                 = BIT1 (m * (2*n + 1) + n)           *)
      eq_sym_rule (spec_rule `m*(2*n+1) + n` bit1_multadddef_thm);
      (* |- ...                 = BIT1 ((2*(m*n) + m) + n)           *)
      mk_comb2_rule `BIT1`
        (list_eq_trans_rule
           [ (* |- m * (2 * n + 1) + n = (2 * (m * n) + m) + n        *)
             mk_bin1_rule `$+`
               (eq_trans_rule
                 (list_spec_rule [m;`2*n`;`1`] mult_dist_right_add_thm)
                 (mk_bin_rule `$+`
                   (list_spec_rule [m;`2`;n] (get_lemma"mult_left_flip_lemma"))
                   (spec_rule m mult_id_thm) ) )
               n;
             (* |- ...                 = 2*(m*n) + (m + n)            *)
             eq_sym_rule (list_spec_rule [`2*(m*n)`;m;n] add_assoc_thm);
             (* |- ...                 = BIT0 (m*n) + (m + n)         *)
             mk_bin1_rule `$+`
               (eq_sym_rule (spec_rule `m*n` bit0_multdef_thm)) `m+n` ])
     ];;

let bit1_squared_lemma =  (* |- (BIT1 m) * (BIT1 m) = BIT1 (BIT0 (m * m + m)) *)
  eq_trans_rule
    (* |- BIT1 m * BIT1 m = BIT1 (BIT0 (m * m) + m)                 *)
    (inst_rule [(m,m);(n,m)] bit1_mult_bit1_lemma)
    (* |- BIT1 (BIT0 (m * m) + (m + m)) = BIT1 (2 * (m*m) + 2 * m)  *)
    (mk_comb2_rule `BIT1`
      (list_eq_trans_rule
         [ (* |- BIT0 (m * m) + (m + m) = 2 * (m*m) + 2 * m             *)
           mk_bin_rule `$+`
             (spec_rule `m*m` bit0_multdef_thm)
             (eq_sym_rule (spec_rule m twice_thm));
           (* |- ...                    = 2 * (m * m + m)               *)
           eq_sym_rule
             (list_spec_rule [`2`;`m*m`;m] mult_dist_right_add_thm);
           (* |- ...                    = BIT0 (m * m + m)              *)
           eq_sym_rule (spec_rule `m * m + m` bit0_multdef_thm) ]));;


(* eval_mult_conv : term -> thm                                               *)
(*                                                                            *)
(* This is the evaluation conversion for numeral multiplication.  It takes a  *)
(* term of the form `m * m`, where "m" and "n" are both natural number        *)
(* numerals, and returns a theorem stating that this equals its numeral       *)
(* value, under no assumptions.                                               *)
(*                                                                            *)
(*       `m * n`                                                              *)
(*    ------------                                                            *)
(*    |- m * n = z                                                            *)

let rec eval_mult_conv0 tm1 tm2 =
  match (dest_bit1 tm1, dest_bit1 tm2) with
    (Zero, _)
       -> (*  0 * n  -->  0                                  *)
          inst_rule [(n,tm2)] zero_mult_lemma
  | (_, Zero)
       -> (*  n * 0  -->  0                                  *)
          inst_rule [(n,tm1)] mult_zero_lemma
  | (One, _)
       -> (*  1 * n  -->  n                                  *)
          inst_rule [(n,tm2)] one_mult_lemma
  | (_, One)
       -> (*  n * 1  -->  n                                  *)
          inst_rule [(n,tm1)] mult_one_lemma
  | (Bit0 tm01, _)
       -> (*  BIT0 m * n  -->  BIT0 (m * n)                  *)
          eq_trans_rule (inst_rule [(m,tm01);(n,tm2)] bit0_mult_lemma)
                        (mk_comb2_rule bit0_fn (eval_mult_conv0 tm01 tm2))
  | (_, Bit0 tm02)
       -> (*  m * BIT0 n  -->  BIT0 (m * n)                  *)
          eq_trans_rule (inst_rule [(m,tm1);(n,tm02)] mult_bit0_lemma)
                        (mk_comb2_rule bit0_fn (eval_mult_conv0 tm1 tm02))
  | (Bit1 tm01, Bit1 tm02)
       -> let th0 = eval_mult_conv0 tm01 tm02 in
          if (tm01 = tm02)
            then (*  BIT1 m * BIT1 m  -->  BIT1 (BIT0 (m*m + m))       *)
                 eq_trans_rule
                   (inst_rule [(m,tm01)] bit1_squared_lemma)
                   (mk_comb2_rule bit1_fn
                     (mk_comb2_rule bit0_fn
                       (eq_trans_rule (mk_bin1_rule `$+` th0 tm01)
                                      (eval_add_conv0 (eqthm_rhs th0) tm01))))
            else (*  BIT1 m * BIT1 n  -->  BIT1 (BIT0 (m*n) + (m+n))   *)
                 let th00 = eval_add_conv0 tm01 tm02 in
                 eq_trans_rule
                   (inst_rule [(m,tm01);(n,tm02)] bit1_mult_bit1_lemma)
                   (mk_comb2_rule bit1_fn
                     (eq_trans_rule
                       (mk_bin_rule `$+` (mk_comb2_rule bit0_fn th0) th00)
                       (eval_add_conv0 (mk_comb (bit0_fn, eqthm_rhs th0))
                                       (eqthm_rhs th00) )));;

let eval_mult_conv tm =
  let func = "eval_mult_conv" in
  let (tm1,tm2) = try1 dest_mult tm   (func, "Not a '*' expression") in
  let () = assert1 (is_nat tm1)        (func, "'*' 1st arg is not a numeral") in
  let () = assert1 (is_nat tm2)        (func, "'*' 2nd arg is not a numeral") in
  let tm01 = dest_numeral_tag tm1 in
  let tm02 = dest_numeral_tag tm2 in
  numeralise_bin_rule (eval_mult_conv0 tm01 tm02);;



(* ** EXPONENTIATION EVALUATION ** *)


(* Evaluation lemmas *)

let exp_bit0_lemma =     (* |- m EXP (BIT0 n) = (m EXP n) * (m EXP n)       *)
  eq_trans_rule
    (* |- m EXP (BIT0 n) = m EXP (n + n)             *)
    (mk_bin2_rule `$EXP` m (spec_rule n bit0_adddef_thm))
    (* |- ...            = (m EXP n) * (m EXP n)     *)
    (list_spec_rule [m;n;n] exp_dist_right_add_thm);;

let exp_bit1_lemma =     (* |- m EXP (BIT1 n) = m * ((m EXP n) * (m EXP n)) *)
  list_eq_trans_rule
     [ (* |- m EXP (BIT1 n) = m EXP (SUC (n + n))        *)
       mk_bin2_rule `$EXP` m (spec_rule n bit1_adddef_thm);
       (* |- ...            = m * (m EXP (n + n))        *)
       list_spec_rule [m;`n+n`] exp_dist_right_suc_thm;
       (* |- ...            = m * (m EXP n * m EXP n)    *)
       mk_bin2_rule `$*` m (list_spec_rule [m;n;n] exp_dist_right_add_thm) ];;

let exp_zero_lemma =     (* |- m EXP ZERO = BIT1 ZERO                       *)
  subs_rule [numeral_zero_thm; numeral_one_thm]
    (spec_rule m exp_right_zero_thm);;

let exp_one_lemma =      (* |- m EXP BIT1 ZERO = m                          *)
  subs_rule [numeral_one_thm] (spec_rule m exp_right_id_thm);;


(* eval_exp_conv : term -> thm                                                *)
(*                                                                            *)
(* This is the evaluation conversion for numeral exponentiation.  It takes a  *)
(* term of the form `m EXP n`, where "m" and "n" are both natural number      *)
(* numerals, and returns a theorem stating that this equals its numeral       *)
(* value, under no assumptions.                                               *)
(*                                                                            *)
(*       `m EXP n`                                                            *)
(*    --------------                                                          *)
(*    |- m EXP n = z                                                          *)

let rec eval_exp_conv0 tm1 tm2 =
  match (dest_bit1 tm2) with
    Bit0 tm02
       -> (*  m EXP (BIT0 n)  -->  (m EXP n) * (m EXP n)          *)
          let th1 = eval_exp_conv0 tm1 tm02 in
          let tm0 = eqthm_rhs th1 in
          list_eq_trans_rule
             [ inst_rule [(m,tm1);(n,tm02)] exp_bit0_lemma;
               mk_bin_rule `$*` th1 th1;
               eval_mult_conv0 tm0 tm0 ]
  | Bit1 tm02
       -> (*  m EXP (BIT1 n)  -->   m * ((m EXP n) * (m EXP n))   *)
          let th1 = eval_exp_conv0 tm1 tm02 in
          let tm0 = eqthm_rhs th1 in
          let th2 = eval_mult_conv0 tm0 tm0 in
          list_eq_trans_rule
             [ inst_rule [(m,tm1);(n,tm02)] exp_bit1_lemma;
               mk_bin2_rule `$*` tm1
                 (eq_trans_rule (mk_bin_rule `$*` th1 th1) th2);
               eval_mult_conv0 tm1 (eqthm_rhs th2) ]
  | One
       -> (*  m EXP 1  -->  m                                     *)
          inst_rule [(m,tm1)] exp_one_lemma
  | Zero
       -> (*  m EXP 0  -->  1                                     *)
          inst_rule [(m,tm1)] exp_zero_lemma;;

let eval_exp_conv tm =
  let func = "eval_exp_conv" in
  let (tm1,tm2) = try1 dest_exp tm   (func, "Not an 'EXP' expression") in
  let () = assert1 (is_nat tm1)      (func, "'EXP' 1st arg is not a numeral") in
  let () = assert1 (is_nat tm2)      (func, "'EXP' 1st arg is not a numeral") in
  let tm01 = dest_numeral_tag tm1 in
  let tm02 = dest_numeral_tag tm2 in
  numeralise_bin_rule (eval_exp_conv0 tm01 tm02);;



(* ** EVEN EVALUATION ** *)


(* Evaluation lemmas *)

let bit0_even_lemma =           (* |- EVEN (BIT0 n) <=> true     *)
  eq_trans_rule
    (* |- EVEN (BIT0 n) <=> EVEN (2 * n)        *)
    (mk_comb2_rule `EVEN` (spec_rule n bit0_multdef_thm))
    (* |- EVEN (2 * n) <=> true                 *)
    (eqt_intro_rule (spec_rule n twice_even_thm));;


let bit1_not_even_lemma =       (* |- EVEN (BIT1 n) <=> false    *)
  list_eq_trans_rule
    [ (* |- EVEN (BIT1 n) <=> EVEN (SUC (2 * n))     *)
      mk_comb2_rule `EVEN` (spec_rule n bit1_multdef_thm);
      (* |- ...           <=> ~ ODD (SUC (2 * n))    *)
      eq_sym_rule
        (eq_trans_rule (mk_not_rule (spec_rule `SUC (2*n)` odd_def))
                       (spec_rule `EVEN (SUC (2*n))` not_dneg_thm) );
      (* |- ...           <=> false                  *)
      mk_not_rule (eqt_intro_rule (spec_rule n suc_twice_odd_thm));
      not_true_thm ];;

let zero_even_lemma =
  subs_rule [numeral_zero_thm] (eqt_intro_rule zero_even_thm);;


(* eval_even_conv : term -> thm                                               *)
(*                                                                            *)
(* This is the evaluation conversion for numeral evenness.  It takes a term   *)
(* of the form `EVEN n`, where "n" is a natural number numeral, and returns   *)
(* a theorem stating its boolean value, under no assumptions.                 *)
(*                                                                            *)
(*        `EVEN n`                                                            *)
(*    ---------------                                                         *)
(*    |- EVEN n <=> z                                                         *)

let rec eval_even_conv0 tm =
  match (dest_bit tm) with
    Bit0 tm00
       -> (*  EVEN (BIT0 n)  -->  true        *)
          inst_rule [(n,tm00)] bit0_even_lemma
  | Bit1 tm00
       -> (*  EVEN (BIT1 n)  -->  false       *)
          inst_rule [(n,tm00)] bit1_not_even_lemma
  | Zero
       -> (*  EVEN 0  -->  true               *)
          zero_even_lemma
  | _  -> internal_error "eval_even_conv0";;

let eval_even_conv tm =
  let func = "eval_even_conv" in
  let tm0 = try1 dest_even tm     (func, "Not an 'EVEN' expression") in
  let () = assert1 (is_nat tm0)   (func, "'EVEN' arg is not a numeral") in
  let tm00 = dest_numeral_tag tm0 in
  numeralise_pred_rule (eval_even_conv0 tm00);;



(* ** ODD EVALUATION ** *)


(* Evaluation lemmas *)

let bit0_not_odd_lemma =        (* |- ODD (BIT0 n) <=> false     *)
  list_eq_trans_rule
    [ (* |- ODD (BIT0 n) <=> ~ EVEN (BIT0 n)      *)
      spec_rule `BIT0 n` odd_def;
      (* |- ...          <=> false                *)
      mk_not_rule bit0_even_lemma;
      not_true_thm ];;

let bit1_odd_lemma =            (* |- ODD (BIT1 n) <=> true     *)
  list_eq_trans_rule
    [ (* |- ODD (BIT1 n) <=> ~ EVEN (BIT1 n)      *)
      spec_rule `BIT1 n` odd_def;
      (* |- ...          <=> true                 *)
      mk_not_rule bit1_not_even_lemma;
      not_false_thm ];;

let zero_not_odd_lemma =
  subs_rule [numeral_zero_thm] (eqf_intro_rule zero_not_odd_thm);;


(* eval_odd_conv : term -> thm                                                *)
(*                                                                            *)
(* This is the evaluation conversion for numeral oddness.  It takes a term of *)
(* the form `ODD n`, where "n" is a natural number numeral, and returns a     *)
(* theorem stating its boolean value, under no assumptions.                   *)
(*                                                                            *)
(*        `ODD n`                                                             *)
(*    --------------                                                          *)
(*    |- ODD n <=> z                                                          *)

let rec eval_odd_conv0 tm =
  match (dest_bit tm) with
    Bit0 tm00
       -> (*  ODD (BIT0 n)  -->  false        *)
          inst_rule [(n,tm00)] bit0_not_odd_lemma
  | Bit1 tm00
       -> (*  ODD (BIT1 n)  -->  true         *)
          inst_rule [(n,tm00)] bit1_odd_lemma
  | Zero
       -> (*  ODD 0  -->  false               *)
          zero_not_odd_lemma
  | _  -> internal_error "eval_odd_conv0";;

let eval_odd_conv tm =
  let func = "eval_odd_conv" in
  let tm0 = try1 dest_odd tm      (func, "Not an 'ODD' expression") in
  let () = assert1 (is_nat tm0)   (func, "'ODD' arg is not a numeral") in
  let tm00 = dest_numeral_tag tm0 in
  numeralise_pred_rule (eval_odd_conv0 tm00);;



(* ** EQUALITY EVALUATION ** *)


(* Evaluation theorems *)

let bit0_eq_zero_lemma =        (* |- BIT0 n = ZERO <=> n = ZERO    *)
  subs_rule [numeral_zero_thm]
   (list_eq_trans_rule
      [ (* |- BIT0 n = 0 <=> 2 * n = 0            *)
        mk_eq1_rule (spec_rule n bit0_multdef_thm) `0`;
        (* |- ...        <=> 2 = 0 \/ n = 0       *)
        list_spec_rule [`2`;n] mult_eq_zero_thm;
        (* |- ...        <=> n = 0                *)
        mk_disj1_rule (eqf_intro_rule two_not_zero_thm) `n=0`;
        list_spec_rule [`false`;`n=0`] disj_comm_thm;
        spec_rule `n=0` disj_id_thm ]);;

let zero_eq_bit0_lemma =        (* |- ZERO = BIT0 n <=> n = ZERO    *)
  eq_trans_rule (eq_sym_conv `ZERO = BIT0 n`) bit0_eq_zero_lemma;;

let bit1_eq_zero_lemma =        (* |- BIT1 n = ZERO <=> false       *)
  eq_trans_rule
    (* |- BIT1 n = 0 <=> SUC (n + n) = 0        *)
    (mk_eq1_rule (spec_rule n bit1_adddef_thm) `ZERO`)
    (* |-            <=> false                  *)
    (eqf_intro_rule (spec_rule `n+n` suc_not_zero_thm0));;

let zero_eq_bit1_lemma =        (* |- ZERO = BIT1 n <=> false       *)
  eq_trans_rule (eq_sym_conv `ZERO = BIT1 n`) bit1_eq_zero_lemma;;

let bit0_eq_bit0_lemma =        (* |- BIT0 m = BIT0 n <=> m = n   *)
  eq_trans_rule
    (* |- BIT0 m = BIT0 n <=> 2 * m = 2 * n     *)
    (mk_eq_rule (spec_rule m bit0_multdef_thm)
                (spec_rule n bit0_multdef_thm))
    (* |- ...             <=> m = n             *)
    (mp_rule
      (list_spec_rule [`2`;m;n] mult_eq_cancel_thm)
      two_not_zero_thm);;

let bit0_eq_bit1_lemma =        (* |- BIT0 m = BIT1 n <=> false   *)
  eqf_intro_rule
    (not_intro_rule
      (disch_rule `BIT0 m = BIT1 n`
        (* BIT0 m = BIT1 n |- false                *)
        (eq_mp_rule
          (* |- EVEN (SUC (2 * n)) <=> false         *)
          (eqf_intro_rule
            (eq_mp_rule
              (spec_rule `SUC (2*n)` odd_def)
              (spec_rule n suc_twice_odd_thm) ))
          (eq_mp_rule
            (* BIT0 m = BIT1 n |- EVEN (2 * m) <=> EVEN (SUC (2 * n))    *)
            (mk_comb2_rule `EVEN`
              (* BIT0 m = BIT1 n |- 2 * m = SUC (2 * n)                    *)
              (eq_mp_rule
                (mk_eq_rule (spec_rule m bit0_multdef_thm)
                            (spec_rule n bit1_multdef_thm) )
                (assume_rule `BIT0 m = BIT1 n`) ))
            (* |- EVEN (2 * m)                                           *)
            (spec_rule m twice_even_thm) ))));;

let bit1_eq_bit0_lemma =        (* |- BIT0 m = BIT1 n <=> false   *)
  eq_trans_rule
    (eq_sym_conv `BIT1 m = BIT0 n`)
    (inst_rule [(m,n);(n,m)] bit0_eq_bit1_lemma);;

let bit1_eq_bit1_lemma =        (* |- BIT1 m = BIT1 n <=> m = n   *)
  list_eq_trans_rule
    [ (* |- BIT1 m = BIT1 n <=> SUC (2 * m) = SUC (2 * n)  *)
      mk_eq_rule (spec_rule m bit1_multdef_thm)
                 (spec_rule n bit1_multdef_thm);
      (* |- ...             <=> 2 * m = 2 * n              *)
      list_spec_rule [`2*m`;`2*n`] suc_injective_thm;
      (* |- ...             <=> m = n                      *)
      mp_rule
        (list_spec_rule [`2`;m;n] mult_eq_cancel_thm)
        two_not_zero_thm ];;

let eq_refl_lemma =             (* |- n = n <=> true              *)
  eqt_intro_rule (eq_refl_conv n);;


(* eval_nat_eq_conv : term -> thm                                             *)
(*                                                                            *)
(* This is the evaluation conversion for numeric equality.  It takes a term   *)
(* of the form `m = n`, where "m" and "n" are both natural number numerals,   *)
(* and returns a theorem stating that this equals its boolean value, under no *)
(* assumptions.                                                               *)
(*                                                                            *)
(*        `m = n`                                                             *)
(*    --------------                                                          *)
(*    |- m = n <=> z                                                          *)

let rec eval_nat_eq_conv0 tm1 tm2 =
  if (tm1 = tm2)
     then (*  n = n  -->  true                    *)
          inst_rule [(n,tm1)] eq_refl_lemma
  else match (dest_bit tm1, dest_bit tm2) with
    (Bit0 tm01, Bit0 tm02)
       -> (*  BIT0 m = BIT0 n  -->  m = n         *)
          eq_trans_rule (inst_rule [(m,tm01);(n,tm02)] bit0_eq_bit0_lemma)
                        (eval_nat_eq_conv0 tm01 tm02)
  | (Bit0 tm01, Bit1 tm02)
       -> (*  BIT0 m = BIT1 n  -->  false         *)
          inst_rule [(m,tm01);(n,tm02)] bit0_eq_bit1_lemma
  | (Bit1 tm01, Bit0 tm02)
       -> (*  BIT1 m = BIT0 n  -->  false         *)
          inst_rule [(m,tm01);(n,tm02)] bit1_eq_bit0_lemma
  | (Bit1 tm01, Bit1 tm02)
       -> (*  BIT1 m = BIT1 n  -->  m = n         *)
          eq_trans_rule (inst_rule [(m,tm01);(n,tm02)] bit1_eq_bit1_lemma)
                        (eval_nat_eq_conv0 tm01 tm02)
  | (Bit0 tm01, Zero)
       -> (*  BIT0 n = ZERO  -->  n = ZERO        *)
          eq_trans_rule (inst_rule [(n,tm01)] bit0_eq_zero_lemma)
                        (eval_nat_eq_conv0 tm01 `ZERO`)
  | (Bit1 tm01, Zero)
       -> (*  BIT1 n = ZERO  -->  false           *)
          inst_rule [(n,tm01)] bit1_eq_zero_lemma
  | (Zero, Bit0 tm02)
       -> (*  ZERO = BIT0 n  -->  n = ZERO        *)
          eq_trans_rule (inst_rule [(n,tm02)] zero_eq_bit0_lemma)
                        (eval_nat_eq_conv0 tm02 `ZERO`)
  | (Zero, Bit1 tm01)
       -> (*  ZERO = BIT1 n  -->  false           *)
          inst_rule [(n,tm01)] zero_eq_bit1_lemma
  | _  -> internal_error "eval_nat_eq_conv0";;

let eval_nat_eq_conv tm =
  let func = "eval_nat_eq_conv" in
  let (tm1,tm2) = try1 dest_eq tm     (func, "Not an '=' expression") in
  let () = assert1 (is_nat tm1)       (func, "'=' 1st arg is not a numeral") in
  let () = assert1 (is_nat tm2)       (func, "'=' 2nd arg is not a numeral") in
  let tm01 = dest_numeral_tag tm1 in
  let tm02 = dest_numeral_tag tm2 in
  numeralise_rel_rule (eval_nat_eq_conv0 tm01 tm02);;



(* ** LE AND LT ** *)


(* Evaluation theorems (<=) *)

let zero_le_lemma =             (* |- ZERO <= n <=> true           *)
  eqt_intro_rule (subs_rule [numeral_zero_thm] (spec_rule n zero_le_thm));;

let le_zero_lemma =             (* |- n <= ZERO <=> n = ZERO       *)
  subs_rule [numeral_zero_thm] (spec_rule n le_zero_thm);;

let bit0_le_bit0_lemma =        (* |- BIT0 m <= BIT0 n <=> m <= n  *)
  eq_trans_rule
    (* |- BIT0 m <= BIT0 n <=> 2 * m <= 2 * n   *)
    (mk_bin_rule `$<=` (spec_rule m bit0_multdef_thm)
                       (spec_rule n bit0_multdef_thm))
    (* |- ...             <=> m <= n            *)
    (mp_rule
      (list_spec_rule [`2`;m;n] mult_le_cancel_thm)
      two_not_zero_thm);;

let bit1_le_bit1_lemma =        (* |- BIT1 m <= BIT1 n <=> m <= n   *)
  list_eq_trans_rule
    [ (* |- BIT1 m <= BIT1 n <=> SUC (2 * m) <= SUC (2 * n)  *)
      mk_bin_rule `$<=` (spec_rule m bit1_multdef_thm)
                        (spec_rule n bit1_multdef_thm);
      (* |- ...              <=> 2 * m <= 2 * n              *)
      list_spec_rule [`2*m`;`2*n`] suc_le_cancel_thm;
      (* |- ...              <=> m <= n                      *)
      mp_rule
        (list_spec_rule [`2`;m;n] mult_le_cancel_thm)
        two_not_zero_thm ];;

let bit1_le_bit0_lemma =       (* |- BIT1 m <= BIT0 n <=> m < n     *)
  list_eq_trans_rule
    [ (* |- BIT1 m <= BIT0 n <=> SUC (2 * m) <= 2 * n    *)
      mk_bin_rule `$<=` (spec_rule m bit1_multdef_thm)
                        (spec_rule n bit0_multdef_thm);
      (* |- ...              <=> 2 * m < 2 * n           *)
      list_spec_rule [`2*m`;`2*n`] suc_le_lt_thm;
      (* |- ...              <=> m < n                   *)
      mp_rule (list_spec_rule [`2`;m;n] mult_lt_cancel_thm)
              two_not_zero_thm ];;

let bit0_le_bit1_lemma =       (* |- BIT0 m <= BIT1 n <=> m <= n    *)
  list_eq_trans_rule
    [ (* |- BIT0 m <= BIT1 n <=> BIT0 m < BIT1 n \/ BIT0 m = BIT1 n   *)
      list_spec_rule [`BIT0 m`;`BIT1 n`] le_cases_thm;
      (* |- ...              <=> BIT0 m < BIT1 n                      *)
      mk_disj2_rule `BIT0 m < BIT1 n` bit0_eq_bit1_lemma;
      spec_rule `BIT0 m < BIT1 n` disj_id_thm;
      (* |- ...              <=> 2 * m < SUC (2 * n)                  *)
      mk_bin_rule `$<` (spec_rule m bit0_multdef_thm)
                       (spec_rule n bit1_multdef_thm);
      (* |- ...              <=> 2 * m <= 2 * n                       *)
      list_spec_rule [`2*m`;`2*n`] lt_suc_le_thm;
      (* |- ...              <=> m <= n                               *)
      mp_rule (list_spec_rule [`2`;m;n] mult_le_cancel_thm)
              two_not_zero_thm ];;

let le_refl_lemma =             (* |- n <= n <=> true             *)
  eqt_intro_rule (spec_rule n le_refl_thm);;


(* Evaluation theorems (<) *)

let zero_lt_lemma =              (* |- ZERO < n <=> ~ (n = ZERO)    *)
  subs_rule [numeral_zero_thm] (spec_rule n zero_lt_thm);;

let lt_zero_lemma =              (* |- n < ZERO <=> false           *)
  eqf_intro_rule (subs_rule [numeral_zero_thm] (spec_rule n not_lt_zero_thm));;

let bit0_lt_bit0_lemma =         (* |- BIT0 m < BIT0 n <=> m < n    *)
  eq_trans_rule
    (* |- BIT0 m < BIT0 n <=> 2 * m < 2 * n      *)
    (mk_bin_rule `$<` (spec_rule m bit0_multdef_thm)
                      (spec_rule n bit0_multdef_thm))
    (mp_rule
      (list_spec_rule [`2`;m;n] mult_lt_cancel_thm)
      two_not_zero_thm);;

let bit1_lt_bit0_lemma =         (* |- BIT1 m < BIT0 n <=> m < n   *)
  list_eq_trans_rule
    [ (* |- BIT1 m < BIT0 n <=> 2 * m + 1 < 2 * n        *)
      mk_bin_rule `$<` (spec_rule m bit1_multadddef_thm)
                       (spec_rule n bit0_multdef_thm);
      (* |- ...             <=> 2 * m + 2 <= 2 * n       *)
      eq_sym_rule (list_spec_rule [`2*m+1`;`2*n`] suc_le_lt_thm);
      mk_bin1_rule `$<=`
        (eq_trans_rule
          (eq_sym_rule (list_spec_rule [`2*m`;`1`] add_dist_right_suc_thm))
          (mk_bin2_rule `$+` `2*m` suc_one_thm) )
        `2*n`;
      (* |- ...             <=> 2 * (m + 1) <= 2 * n     *)
      mk_bin1_rule `$<=`
        (eq_trans_rule
          (eq_sym_rule (mk_bin2_rule `$+` `2*m` (spec_rule `2` mult_id_thm)))
          (eq_sym_rule (list_spec_rule [`2`;m;`1`] mult_dist_right_add_thm)) )
        `2*n`;
      (* |- ...             <=> m + 1 <= n               *)
      mp_rule (list_spec_rule [`2`;`m+1`;n] mult_le_cancel_thm)
              two_not_zero_thm;
      (* |- ...             <=> m < n                    *)
      eq_sym_rule (mk_bin1_rule `$<=` (spec_rule m suc_add_thm) n);
      list_spec_rule [m;n] suc_le_lt_thm ];;

let bit0_lt_bit1_lemma =         (* |- BIT0 m < BIT1 n <=> m <= n  *)
  list_eq_trans_rule
    [ (* |- BIT0 m < BIT1 n <=> 2 * m < SUC (2 * n)      *)
      mk_bin_rule `$<` (spec_rule m bit0_multdef_thm)
                       (spec_rule n bit1_multdef_thm);
      (* |- ...             <=> 2 * m <= 2 * n           *)
      list_spec_rule [`2*m`;`2*n`] lt_suc_le_thm;
      (* |- ...             <=> m <= n                   *)
      mp_rule (list_spec_rule [`2`;m;n] mult_le_cancel_thm)
              two_not_zero_thm ];;

let bit1_lt_bit1_lemma =         (* |- BIT1 m < BIT1 n <=> m < n   *)
  list_eq_trans_rule
    [ (* |- BIT1 m < BIT1 n <=> SUC (2 * m) < SUC (2 * n)    *)
      mk_bin_rule `$<` (spec_rule m bit1_multdef_thm)
                       (spec_rule n bit1_multdef_thm);
      (* |- ...             <=> 2 * m < 2 * n                *)
      list_spec_rule [`2*m`;`2*n`] suc_lt_cancel_thm;
      (* |- ...             <=> m < n                        *)
      mp_rule
        (list_spec_rule [`2`;m;n] mult_lt_cancel_thm)
        two_not_zero_thm ];;

let lt_irrefl_lemma =             (* |- n < n <=> false            *)
  eqf_intro_rule (spec_rule n lt_irrefl_thm);;


(* eval_lt_conv : term -> thm                                                 *)
(* eval_le_conv : term -> thm                                                 *)
(*                                                                            *)
(* These are the evaluation conversions for numeral less-than and less-than-  *)
(* or-equal comparison.  They take a term of the form `m < n` or `m <= n`     *)
(* respectively, where "m" and "n" are both natural number numerals, and      *)
(* returns a theorem stating that this input equals its boolean value, under  *)
(* no assumptions.                                                            *)
(*                                                                            *)
(*        `m < n`                   `m <= n`                                  *)
(*    --------------            ---------------                               *)
(*    |- m < n <=> z            |- m <= n <=> z                               *)

(* It is necessary to implement '<=' and '<' evaluation as mutually recursive *)
(* because each have a case that reduces to the other (BIT1-BIT0 for '<=' and *)
(* BIT0-BIT1 for '<').                                                        *)

let rec eval_le_conv0 tm1 tm2 =
  if (tm1 = tm2)
     then (*  n <= n  -->  true                    *)
          inst_rule [(n,tm1)] le_refl_lemma
  else match (dest_bit tm1, dest_bit tm2) with
    (Bit0 tm01, Bit0 tm02)
       -> (*  BIT0 m <= BIT0 n  -->  m <= n        *)
          eq_trans_rule (inst_rule [(m,tm01);(n,tm02)] bit0_le_bit0_lemma)
                        (eval_le_conv0 tm01 tm02)
  | (Bit0 tm01, Bit1 tm02)
       -> (*  BIT0 m <= BIT1 y  -->  m <= n        *)
          eq_trans_rule (inst_rule [(m,tm01);(n,tm02)] bit0_le_bit1_lemma)
                        (eval_le_conv0 tm01 tm02)
  | (Bit1 tm01, Bit0 tm02)
       -> (*  BIT1 m <= BIT0 n  -->  m < n         *)
          eq_trans_rule (inst_rule [(m,tm01);(n,tm02)] bit1_le_bit0_lemma)
                        (eval_lt_conv0 tm01 tm02)
  | (Bit1 tm01, Bit1 tm02)
       -> (*  BIT1 m <= BIT1 n  -->  m <= n        *)
          eq_trans_rule (inst_rule [(m,tm01);(n,tm02)] bit1_le_bit1_lemma)
                        (eval_le_conv0 tm01 tm02)
  | (_, Zero)
       -> (*  BITX n <= ZERO  -->  n = ZERO        *)
          eq_trans_rule (inst_rule [(n,tm1)] le_zero_lemma)
                        (eval_nat_eq_conv0 tm1 `ZERO`)
  | (Zero, _)
       -> (*  ZERO <= n  -->  true                 *)
          inst_rule [(n,tm2)] zero_le_lemma
  | _  -> internal_error "eval_le_conv0"

and eval_lt_conv0 tm1 tm2 =
  if (tm1 = tm2)
     then (*  n < n  -->  false                    *)
          inst_rule [(n,tm1)] lt_irrefl_lemma
  else match (dest_bit tm1, dest_bit tm2) with
    (Bit0 tm01, Bit0 tm02)
       -> (*  BIT0 m < BIT0 n  -->  m < n          *)
          eq_trans_rule (inst_rule [(m,tm01);(n,tm02)] bit0_lt_bit0_lemma)
                        (eval_lt_conv0 tm01 tm02)
  | (Bit0 tm01, Bit1 tm02)
       -> (*  BIT0 m < BIT1 n  -->  m <= n         *)
          eq_trans_rule (inst_rule [(m,tm01);(n,tm02)] bit0_lt_bit1_lemma)
                        (eval_le_conv0 tm01 tm02)
  | (Bit1 tm01, Bit0 tm02)
       -> (*  BIT1 m < BIT0 n  -->  m < n          *)
          eq_trans_rule (inst_rule [(m,tm01);(n,tm02)] bit1_lt_bit0_lemma)
                        (eval_lt_conv0 tm01 tm02)
  | (Bit1 tm01, Bit1 tm02)
       -> (*  BIT1 m < BIT1 n  -->  m < n          *)
          eq_trans_rule (inst_rule [(m,tm01);(n,tm02)] bit1_lt_bit1_lemma)
                        (eval_lt_conv0 tm01 tm02)
  | (Zero, _)
       -> (*  ZERO < n  -->  ~ (n = ZERO)          *)
          list_eq_trans_rule
             [ inst_rule [(n,tm2)] zero_lt_lemma;
               mk_comb2_rule `$~` (eval_nat_eq_conv0 tm2 `ZERO`);
               not_false_thm ]
  | (_, Zero)
       -> (*  n < ZERO  -->  false                 *)
          inst_rule [(n,tm1)] lt_zero_lemma
  | _  -> internal_error "eval_lt_conv0";;

let eval_le_conv tm =
  let func = "eval_le_conv" in
  let (tm1,tm2) = try1 dest_le tm     (func, "Not a '<=' expression") in
  let () = assert1 (is_nat tm1)       (func, "'<=' 1st arg is not a numeral") in
  let () = assert1 (is_nat tm2)       (func, "'<=' 2nd arg is not a numeral") in
  let tm01 = dest_numeral_tag tm1 in
  let tm02 = dest_numeral_tag tm2 in
  numeralise_rel_rule (eval_le_conv0 tm01 tm02);;

let eval_lt_conv tm =
  let func = "eval_lt_conv" in
  let (tm1,tm2) = try1 dest_lt tm     (func, "Not a '<' expression") in
  let () = assert1 (is_nat tm1)       (func, "'<' 1st arg is not a numeral") in
  let () = assert1 (is_nat tm2)       (func, "'<' 2nd arg is not a numeral") in
  let tm01 = dest_numeral_tag tm1 in
  let tm02 = dest_numeral_tag tm2 in
  numeralise_rel_rule (eval_lt_conv0 tm01 tm02);;



(* ** GE AND GT ** *)


(* Evaluation lemmas *)

let gt_lt_lemma =            (* |- m > n <=> n < m        *)
  list_spec_rule [m;n] gt_def;;

let ge_le_lemma =            (* |- m >= n <=> n =< m      *)
  list_spec_rule [m;n] ge_def;;


(* eval_gt_conv : term -> thm                                                 *)
(* eval_ge_conv : term -> thm                                                 *)
(*                                                                            *)
(* These are the evaluation conversions for numeral greater-than and greater- *)
(* than-or-equal comparison.  They take a term of the form `m > n` or         *)
(* `m >= n` respectively, where "m" and "n" are both natural number numerals, *)
(* and returns a theorem stating that this input equals its boolean value,    *)
(* under no assumptions.                                                      *)
(*                                                                            *)
(*        `m > n`                   `m >= n`                                  *)
(*    --------------            ---------------                               *)
(*    |- m > n <=> z            |- m >= n <=> z                               *)

let eval_gt_conv tm =
  let func = "eval_gt_conv" in
  let (tm1,tm2) = try1 dest_gt tm     (func, "Not a '>' expression") in
  let () = assert1 (is_nat tm1)       (func, "'>' 1st arg is not a numeral") in
  let () = assert1 (is_nat tm2)       (func, "'>' 2nd arg is not a numeral") in
  let tm01 = dest_numeral_tag tm1 in
  let tm02 = dest_numeral_tag tm2 in
  let th = eq_trans_rule (inst_rule [(m,tm01);(n,tm02)] gt_lt_lemma)
                         (eval_lt_conv0 tm02 tm01) in
  numeralise_rel_rule th;;

let eval_ge_conv tm =
  let func = "eval_ge_conv" in
  let (tm1,tm2) = try1 dest_ge tm     (func, "Not a '>=' expression") in
  let () = assert1 (is_nat tm1)       (func, "'>=' 1st arg is not a numeral") in
  let () = assert1 (is_nat tm2)       (func, "'>=' 2nd arg is not a numeral") in
  let tm01 = dest_numeral_tag tm1 in
  let tm02 = dest_numeral_tag tm2 in
  let th = eq_trans_rule (inst_rule [(m,tm01);(n,tm02)] ge_le_lemma)
                         (eval_le_conv0 tm02 tm01) in
  numeralise_rel_rule th;;



(* ** SUBTRACTION EVALUATION ** *)


(* Evaluation lemmas *)

let sub_zero_lemma =        (* |- n - ZERO = n               *)
  subs_rule [numeral_zero_thm] (spec_rule n sub_right_id_thm);;

let sub_cancel_lemma =      (* |- n - n = ZERO               *)
  subs_rule [numeral_zero_thm] (spec_rule n sub_cancel_thm);;

let add_sub_lemma =         (* |- z + n = m ==> m - n = z    *)
  disch_rule `z+n = m`
    (subs_rule
      [assume_rule `z+n = m`]
      (list_spec_rule [z;n] add_sub_cancel_thm) );;


(* eval_sub_conv : term -> thm                                                *)
(*                                                                            *)
(* This is the evaluation conversion for numeral subtraction.  It takes a     *)
(* term of the form `m - n`, where "m" and "n" are both natural number        *)
(* numerals, and returns a theorem stating that this equals its numeral       *)
(* value, under no assumptions.                                               *)
(*                                                                            *)
(*       `m - n`                                                              *)
(*    ------------                                                            *)
(*    |- m - n = z                                                            *)

(* For the non-trivial cases, this is implemented by working out the result   *)
(* `z` in ML and then working backwards from evaluating the `z + n` in HOL.   *)

let sub_floor_thm0 = subs_rule [numeral_zero_thm] sub_floor_thm;;

let eval_sub_conv0 tm1 tm2 =
  let n1 = dest_nat_big_int0 tm1  and n2 = dest_nat_big_int0 tm2 in
  if (eq_big_int n2 big_int_0)
    then (*  n - ZERO  -->  n                         *)
         inst_rule [(n,tm1)] sub_zero_lemma
  else if (eq_big_int n2 n1)
    then (*  n - n  -->  ZERO                         *)
         inst_rule [(n,tm1)] sub_cancel_lemma
  else if (lt_big_int n2 n1)
    then (* [ z + n = m ]  m - n  -->  z              *)
         let tm3 = mk_nat_big_int0 (sub_big_int n1 n2) in
         mp_rule
           (inst_rule [(m,tm1);(n,tm2);(z,tm3)] add_sub_lemma)
           (eval_add_conv0 tm3 tm2)
    else (* [ m < n ]  m - n  -->  ZERO               *)
         mp_rule
           (list_spec_rule [tm1;tm2] sub_floor_thm0)
           (eqt_elim_rule (eval_le_conv0 tm1 tm2));;

let eval_sub_conv tm =
  let func = "eval_sub_conv" in
  let (tm1,tm2) = try1 dest_sub tm    (func, "Not a '-' expression") in
  let () = assert1 (is_nat tm1)       (func, "'-' 1st arg is not a numeral") in
  let () = assert1 (is_nat tm2)       (func, "'-' 2nd arg is not a numeral") in
  let tm01 = dest_numeral_tag tm1 in
  let tm02 = dest_numeral_tag tm2 in
  numeralise_bin_rule (eval_sub_conv0 tm01 tm02);;


end;;
