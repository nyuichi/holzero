(* ========================================================================== *)
(* BOOLEAN ALGEBRA (HOL Zero)                                                 *)
(* - Derived algebraic theorems for predicate logic                           *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2012                            *)
(* ========================================================================== *)


module type BoolAlg_sig = sig

  (* Theorems *)

  val not_true_thm : thm
  val not_false_thm : thm
  val true_not_eq_false_thm : thm

  val not_dist_disj_thm : thm

  val conj_id_thm : thm
  val conj_zero_thm : thm
  val conj_comm_thm : thm
  val conj_assoc_thm : thm
  val conj_idem_thm : thm
  val conj_absorb_disj_thm : thm
  val conj_contr_thm : thm
  val conj_dist_left_disj_thm : thm
  val conj_dist_right_disj_thm : thm

  val disj_id_thm : thm
  val disj_zero_thm : thm
  val disj_comm_thm : thm
  val disj_assoc_thm : thm
  val disj_idem_thm : thm
  val disj_absorb_conj_thm : thm
  val disj_dist_left_conj_thm : thm
  val disj_dist_right_conj_thm : thm

  val imp_left_id_thm : thm
  val imp_left_zero_thm : thm
  val imp_right_zero_thm : thm
  val imp_refl_thm : thm
  val imp_dist_left_disj_thm : thm
  val imp_dist_right_conj_thm : thm
  val imp_imp_thm : thm

  val forall_dist_conj_thm : thm
  val forall_one_point_thm : thm
  val forall_null_thm : thm

end;;
