(* ========================================================================== *)
(* NATURAL NUMBER NUMERALS (HOL Zero)                                         *)
(* - Theory defining natural number numerals                                  *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2010-2013                            *)
(* ========================================================================== *)


module type NatNumrl_sig = sig

  (* Definitions *)

  val bit0_def : thm
  val bit1_def : thm
  val numeral_def : thm

  (* Constants *)

  val zero_tm : term

  (* Syntax functions *)

  val mk_nat : int -> term
  val dest_nat : term -> int

  val mk_nat_big_int : big_int -> term
  val dest_nat_big_int : term -> big_int

  val is_nat : term -> bool

  (* Theorems *)

  val nat_cases_thm : thm
  val nat_induction_thm : thm
  val nat_recursion_thm : thm
  val suc_not_zero_thm : thm

  val one_not_zero_thm : thm
  val two_not_zero_thm : thm

  val suc_zero_thm : thm
  val suc_one_thm : thm

  (* Support for internal representation *)

  val bit0_fn : term
  val bit1_fn : term

  val mk_numeral_tag : term -> term
  val dest_numeral_tag : term -> term

  val mk_nat_big_int0 : big_int -> term
  val dest_nat_big_int0 : term -> big_int

  val numeralise_mono_rule : thm -> thm
  val numeralise_bin_rule : thm -> thm
  val numeralise_pred_rule : thm -> thm
  val numeralise_rel_rule : thm -> thm

  val zero_numeral_thm : thm
  val numeral_zero_thm : thm
  val one_numeral_thm : thm
  val numeral_one_thm : thm

  val suc_zero_thm0 : thm
  val suc_one_thm0 : thm

end;;
