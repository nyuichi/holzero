(* ========================================================================== *)
(* EQUALITY CONGRUENCE RULES (HOL Zero)                                       *)
(* - Derived equality congruence rules                                        *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2012                            *)
(* ========================================================================== *)


module type EqCong_sig = sig

  (* Inference rules *)

  val mk_bin_rule : term -> thm -> thm -> thm
  val mk_bin1_rule : term -> thm -> term -> thm
  val mk_bin2_rule : term -> term -> thm -> thm

  val mk_eq_rule : thm -> thm -> thm
  val mk_eq1_rule : thm -> term -> thm
  val mk_eq2_rule : term -> thm -> thm

  val mk_not_rule : thm -> thm

  val mk_conj_rule : thm -> thm -> thm
  val mk_conj1_rule : thm -> term -> thm
  val mk_conj2_rule : term -> thm -> thm

  val mk_disj_rule : thm -> thm -> thm
  val mk_disj1_rule : thm -> term -> thm
  val mk_disj2_rule : term -> thm -> thm

  val mk_imp_rule : thm -> thm -> thm
  val mk_imp1_rule : thm -> term -> thm
  val mk_imp2_rule : term -> thm -> thm

  val mk_forall_rule : term -> thm -> thm
  val mk_exists_rule : term -> thm -> thm
  val mk_uexists_rule : term -> thm -> thm
  val mk_select_rule : term -> thm -> thm

end;;
