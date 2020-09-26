(* ========================================================================== *)
(* BOOLEANS CLASSICAL (HOL Zero)                                              *)
(* - Derived theorems/rules for predicate logic relying on Axiom of Choice    *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2015                            *)
(* ========================================================================== *)


module type BoolClass_sig = sig

  (* Theorems *)

  val excluded_middle_thm : thm
  val bool_cases_thm : thm

  val imp_disj_thm : thm

  val not_dneg_thm : thm
  val not_dist_conj_thm : thm
  val not_dist_exists_thm : thm
  val not_dist_forall_thm : thm

  val cond_true_thm : thm
  val cond_false_thm : thm
  val cond_idem_thm : thm
  val cond_not_thm : thm

  val exists_dist_disj_thm : thm
  val exists_one_point_thm : thm
  val exists_value_thm : thm
  val exists_null_thm : thm

  val uexists_thm1 : thm
  val uexists_thm2 : thm
  val uexists_thm3 : thm
  val uexists_one_point_thm : thm

  val skolem_thm : thm
  val unique_skolem_thm : thm

  (* Inference rules *)

  val ccontr_rule : term -> thm -> thm
  val exists_rule : term * term -> thm -> thm
  val select_rule : thm -> thm

end;;
