(* ========================================================================== *)
(* NATURAL NUMBER RELATIONS (HOL Zero)                                        *)
(* - Theory defining natural number relations; derived properties             *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2010-2011                            *)
(* ========================================================================== *)


module type NatRel_sig = sig

  (* Definitions *)

  val lt_def : thm
  val le_def : thm
  val gt_def : thm
  val ge_def : thm

  (* Syntax functions *)

  val mk_lt : term * term -> term
  val dest_lt : term -> term * term
  val is_lt : term -> bool

  val mk_le : term * term -> term
  val dest_le : term -> term * term
  val is_le : term -> bool

  val mk_gt : term * term -> term
  val dest_gt : term -> term * term
  val is_gt : term -> bool

  val mk_ge : term * term -> term
  val dest_ge : term -> term * term
  val is_ge : term -> bool

  (* Theorems *)

  val suc_lt_cancel_thm : thm
  val suc_le_cancel_thm : thm

  val add_eq_zero_thm : thm
  val add_eq_cancel_thm : thm
  val add_lt_cancel_thm : thm
  val add_le_cancel_thm : thm

  val mult_eq_zero_thm : thm
  val mult_eq_cancel_thm : thm
  val mult_lt_cancel_thm : thm
  val mult_le_cancel_thm : thm

  val lt_irrefl_thm : thm
  val lt_asym_thm : thm
  val lt_trans_thm : thm
  val lt_zero_cases_thm : thm
  val lt_suc_cases_thm : thm
  val not_lt_cases_thm : thm
  val lt_suc_thm : thm
  val zero_lt_suc_thm : thm
  val not_lt_zero_thm : thm
  val zero_lt_thm : thm

  val le_refl_thm : thm
  val le_antisym_thm : thm
  val le_trans_thm : thm
  val le_cases_thm : thm
  val le_zero_thm : thm
  val zero_le_thm : thm
  val sub_floor_thm : thm
  val suc_le_lt_thm : thm
  val lt_suc_le_thm : thm

end;;
