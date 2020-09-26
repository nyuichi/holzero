(* ========================================================================== *)
(* NATURAL NUMBER NUMERALS (HOL Zero)                                         *)
(* - Theory defining natural number numerals                                  *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2010-2016                            *)
(* ========================================================================== *)


module NatNumrl : NatNumrl_sig = struct


(* This module defines the representation of natural number numerals.  This   *)
(* is based on the HOL functions "BIT0" and "BIT1".                           *)


open Def2;;

open Equal;;
open EqCong;;
open Bool;;

open Nat;;



(* ** BIT0, BIT1 and NUMERAL ** *)

(* The representation of natural number numerals can now be defined, in terms *)
(* of "SUC" and addition.  The representation involves applying a sequence    *)
(* of "BIT0" and "BIT1" operators to the "ZERO" constant, with "NUMERAL" as a *)
(* tag that gets applied to the result.  Both "BIT0" and "BIT1" double their  *)
(* argument and respectively add 0 or 1.  The "NUMERAL" tag simply returns    *)
(* its argument, and is used for identifying numeral atoms in terms.  When    *)
(* read innermost-to-outermost, a sequence of "BIT0"s and "BIT1"s corresponds *)
(* directly to the 0s and 1s of binary notation.                              *)

(* Example, the number 6 is represented by:                                   *)
(*      NUMERAL (BIT0 (BIT1 (BIT1 ZERO)))      (or 110 in binary)             *)


(* NUMERAL *)

let numeral_def = new_fun_definition `!(n:nat). NUMERAL n = n`;;

let numeral_fn = `NUMERAL`;;


(* BIT0 *)

let bit0_def =
  new_recursive_fun_definition nat_recursion_thm0
   `(BIT0 ZERO = ZERO) /\
    (!n. BIT0 (SUC n) = SUC (SUC (BIT0 n)))`;;

let bit0_fn = `BIT0`;;


(* BIT *)

let bit1_def = new_fun_definition `!n. BIT1 n = SUC (BIT0 n)`;;

let bit1_fn = `BIT1`;;


(* Numeral values *)

let zero_tm = `NUMERAL ZERO`;;


(* Syntax functions for numeral tag *)

let mk_numeral_tag tm =
  if (type_of tm = nat_ty)
    then mk_comb (numeral_fn, tm)
    else hol_fail ("mk_numeral_tag", "Not wrapped by 'NUMERAL'");;

let is_numeral_tag tm =
  (is_comb tm) && (term_eq (rator tm) numeral_fn);;

let dest_numeral_tag tm =
  if (is_numeral_tag tm)
    then rand tm
    else hol_fail ("dest_numeral", "Not wrapped by 'NUMERAL'");;


(* Syntax functions for numerals using OCaml's 'big_int' integers *)

let rec mk_nat_big_int0 n =
  if (gt_big_int n big_int_0)
    then let (n0,n1) = quomod_big_int n big_int_2 in
         let f = if (eq_big_int n1 big_int_0) then bit0_fn
                                              else bit1_fn in
         let tm0 = mk_nat_big_int0 n0 in
         mk_comb (f,tm0)
  else if (eq_big_int n big_int_0)
    then zero_tm0
    else hol_fail ("mk_nat_big_int","Arg must not be negative");;

let mk_nat_big_int n = mk_numeral_tag (mk_nat_big_int0 n);;

let rec dest_nat_big_int0 tm =
  try
    let (f,tm0) = try0 dest_comb tm      LocalFail in
    let x = try1 const_name f            ("dest_nat_big_int","Not a numeral") in
    match x with
      "BIT0" -> mult_big_int big_int_2 (dest_nat_big_int0 tm0)
    | "BIT1" -> add_big_int (mult_big_int big_int_2 (dest_nat_big_int0 tm0))
                            big_int_1
    | _      -> hol_fail ("dest_nat_big_int","Not a numeral")
  with LocalFail ->
    if (term_eq tm zero_tm0)
      then big_int_0
      else hol_fail ("dest_nat_big_int","Not a numeral");;

let dest_nat_big_int tm =
  let tm0 = try1 dest_numeral_tag tm   ("dest_nat_big_int","Not a numeral") in
  dest_nat_big_int0 tm0;;


(* Syntax functions based on OCaml's 'int' integers *)

let mk_nat0 n =
  try2 mk_nat_big_int0 (big_int_of_int n)    "mk_nat";;

let mk_nat n = mk_numeral_tag (mk_nat0 n);;

let dest_nat0 tm =
  let n = try2 dest_nat_big_int0 tm      "dest_nat" in
  if (is_int_big_int n)
    then int_of_big_int n
    else hol_fail ("dest_nat", "Not a small-integer numeral");;

let dest_nat tm =
  let tm0 = try1 dest_numeral_tag tm   ("dest_nat","Not a numeral") in
  dest_nat0 tm0;;


(* Disriminator for numerals *)

let rec is_nat0 tm =
  try
    let (f,tm0) = try0 dest_comb tm      LocalFail in
    (term_eq f bit0_fn) || (term_eq f bit1_fn)
  with LocalFail ->
    (term_eq tm zero_tm0);;

let is_nat tm =
  (is_numeral_tag tm) &&
  (is_nat0 (dest_numeral_tag tm));;



(* ** NUMERAL TAG THEOREMS ** *)

(* First a few utility rules for distributing the 'NUMERAL' tag.              *)


(* numeralise_mono_rule                                                       *)
(*                                                                            *)
(*            |- f n = m                                                      *)
(*    ----------------------------                                            *)
(*    |- f (NUMERAL n) = NUMERAL m                                            *)

let numeralise_mono_thm =
  (* |- !f n. f (NUMERAL n) = NUMERAL (f n)   *)
  list_gen_rule [`f:nat->nat`;`n:nat`]
    (eq_trans_rule
      (* |- f (NUMERAL n) = f n                 *)
      (mk_comb2_rule `(f:nat->nat)`
        (spec_rule `n:nat` numeral_def) )
      (* |- f n = NUMERAL (f n)                 *)
      (eq_sym_rule (spec_rule `(f:nat->nat) n` numeral_def)) );;

let numeralise_mono_rule th =        (* |- f n = m              *)
  let (lhs,rhs) = dest_eqthm th in
  let (f,tm0) = dest_comb lhs in
  eq_trans_rule
    (list_spec_rule [f;tm0] numeralise_mono_thm)
                                       (* |- f (NUMERAL n) = NUMERAL (f n)  *)
    (mk_comb2_rule `NUMERAL` th);;     (* |- NUMERAL (f n) = NUMERAL m      *)


(* numeralise_bin_rule                                                        *)
(*                                                                            *)
(*                 |- f n1 n2 = m                                             *)
(*    ------------------------------------------                              *)
(*    |- f (NUMERAL n1) (NUMERAL n2) = NUMERAL m                              *)

let numeralise_bin_thm =
  (* |- !f n1 n2. f (NUMERAL n1) (NUMERAL n2) = NUMERAL (f n1 n2)   *)
  list_gen_rule [`f:nat->nat->nat`;`n1:nat`;`n2:nat`]
    (eq_trans_rule
      (* |- f (NUMERAL n1) (NUMERAL n2) = f n1 n2   *)
      (mk_bin_rule `(f:nat->nat->nat)`
        (spec_rule `n1:nat` numeral_def)
        (spec_rule `n2:nat` numeral_def) )
      (* |- f n1 n2 = NUMERAL (f n1 n2)             *)
      (eq_sym_rule (spec_rule `(f:nat->nat->nat) n1 n2` numeral_def)) );;

let numeralise_bin_rule th =        (* |- f n1 n2 = m              *)
  let (lhs,rhs) = dest_eqthm th in
  let (f,tm1,tm2) = dest_bin lhs in
  eq_trans_rule
    (list_spec_rule [f;tm1;tm2] numeralise_bin_thm)
                      (* |- f (NUMERAL n1) (NUMERAL n2) = NUMERAL (f n1 n2)  *)
    (mk_comb2_rule `NUMERAL` th);;    (* |- NUMERAL (f n1 n2) = NUMERAL m    *)


(* numeralise_pred_rule                                                       *)
(*                                                                            *)
(*         |- P n <=> b                                                       *)
(*    ----------------------                                                  *)
(*    |- P (NUMERAL n) <=> b                                                  *)

let numeralise_pred_rule th =      (* |- f n = m              *)
  let (lhs,rhs) = dest_eqthm th in
  let (p,tm0) = dest_comb lhs in
  eq_trans_rule                      (* |- P (NUMERAL n) = NUMERAL (P n)  *)
    (mk_comb2_rule p (spec_rule tm0 numeral_def))
    th;;


(* numeralise_rel_rule                                                        *)
(*                                                                            *)
(*             |- n1 R n2 <=> b                                               *)
(*    ------------------------------------                                    *)
(*    |- (NUMERAL n1) R (NUMERAL n2) <=> b                                    *)

let numeralise_rel_thm =
  (* |- !R n1 n2. (NUMERAL n1) R (NUMERAL n2) <=> b    *)
  list_gen_rule [`R:nat->nat->bool`;`n1:nat`;`n2:nat`]
    (* |- (NUMERAL n1) R (NUMERAL n2) = n1 R n2          *)
    (mk_bin_rule `(R:nat->nat->bool)`
      (spec_rule `n1:nat` numeral_def)
      (spec_rule `n2:nat` numeral_def) );;

let numeralise_rel_rule th =        (* |- n1 R n2 <=> b              *)
  let (lhs,rhs) = dest_eqthm th in
  let (r,tm1,tm2) = dest_bin lhs in
  eq_trans_rule
    (list_spec_rule [r;tm1;tm2] numeralise_rel_thm)
    th;;



(* ** CONVERTING BETWEEN TAGGED AND UNTAGGED ** *)


let numeral_zero_thm = spec_rule `ZERO` numeral_def;;
let zero_numeral_thm = eq_sym_rule numeral_zero_thm;;

let numeral_one_thm = spec_rule `BIT1 ZERO` numeral_def;;
let one_numeral_thm = eq_sym_rule numeral_one_thm;;



(* ** BASIC NAT PROPERTIES FOR ZERO NUMERAL ** *)


let nat_cases_thm = save_thm ("nat_cases_thm",
  subs_rule [zero_numeral_thm] nat_cases_thm0
);;

let nat_induction_thm = save_thm ("nat_induction_thm",
  subs_rule [zero_numeral_thm] nat_induction_thm0
);;

let nat_recursion_thm = save_thm ("nat_recursion_thm",
  subs_rule [zero_numeral_thm] nat_recursion_thm0
);;

let suc_not_zero_thm = save_thm ("suc_not_zero_thm",
  subs_rule [zero_numeral_thm] suc_not_zero_thm0
);;



(* ** DERIVED THEOREMS ** *)

(* Some useful theorems about specific numerals are now proved.               *)


(* suc_zero_thm                                                               *)
(*                                                                            *)
(*    |- SUC 0 = 1                                                            *)

let suc_zero_thm0 =
  (* |- SUC ZERO = BIT1 ZERO            *)
  eq_trans_rule
    (* |- SUC ZERO = SUC (BIT0 ZERO)      *)
    (eq_sym_rule (mk_comb2_rule `SUC` (conjunct1_rule bit0_def)))
    (* |- SUC (BIT0 ZERO) = BIT1 ZERO     *)
    (eq_sym_rule (spec_rule `ZERO` bit1_def));;

let suc_zero_thm = save_thm ("suc_zero_thm",
  numeralise_mono_rule suc_zero_thm0
);;


(* suc_one_thm                                                                *)
(*                                                                            *)
(*    |- SUC 1 = 2                                                            *)

let suc_one_thm0 =
  (* |- SUC (BIT1 ZERO) = BIT0 (BIT1 ZERO)         *)
  list_eq_trans_rule
    [ (* |- SUC (BIT1 ZERO) = SUC (SUC ZERO)           *)
      eq_sym_rule (mk_comb2_rule `SUC` suc_zero_thm0);
      (* |- SUC (SUC ZERO) = SUC (SUC (BIT0 ZERO))     *)
      eq_sym_rule
        (mk_comb2_rule `SUC`
           (mk_comb2_rule `SUC` (conjunct1_rule bit0_def)));
      (* |- SUC (SUC (BIT0 ZERO)) = BIT0 (SUC ZERO)    *)
      eq_sym_rule (spec_rule `ZERO` (conjunct2_rule bit0_def));
      (* |- BIT0 (SUC ZERO) = BIT0 (BIT1 ZERO)         *)
      mk_comb2_rule `BIT0` suc_zero_thm0 ];;

let suc_one_thm = save_thm ("suc_one_thm",
  numeralise_mono_rule suc_one_thm0
);;


(* one_not_zero_thm                                                           *)
(*                                                                            *)
(*    |- ~ (1 = 0)                                                            *)

let one_not_zero_thm = save_thm ("one_not_zero_thm",
  eq_mp_rule
    (mk_not_rule (mk_eq1_rule suc_zero_thm `0`))
    (spec_rule `0` suc_not_zero_thm)
);;


(* two_not_zero_thm                                                           *)
(*                                                                            *)
(*    |- ~ (2 = 0)                                                            *)

let two_not_zero_thm = save_thm ("two_not_zero_thm",
  eq_mp_rule
    (mk_not_rule (mk_eq1_rule suc_one_thm `0`))
    (spec_rule `1` suc_not_zero_thm)
);;


end;;
