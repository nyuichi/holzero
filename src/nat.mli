(* ========================================================================== *)
(* NATURAL NUMBERS (HOL Zero)                                                 *)
(* - Theory defining natural numbers, plus basic derived properties           *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2010-2013                            *)
(* ========================================================================== *)


module type Nat_sig = sig

  (* Type constants *)

  val nat_ty : hol_type

  (* Syntax functions *)

  val mk_suc : term -> term
  val dest_suc : term -> term
  val is_suc : term -> bool

  (* Definitions *)

  val is_nat_rep_def : thm
  val nat_def : thm
  val nat_bij_def1 : thm
  val nat_bij_def2 : thm

  val zero_def : thm
  val suc_def : thm

  (* Constants *)

  val zero_tm0 : term
  val suc_fn : term

  (* Theorems *)

  val nat_cases_thm0 : thm
  val nat_induction_thm0 : thm
  val nat_recursion_thm0 : thm

  val suc_not_zero_thm0 : thm
  val suc_injective_thm : thm

end;;
