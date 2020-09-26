(* ========================================================================== *)
(* BOOLEANS (HOL Zero)                                                        *)
(* - Extra theory and derived inference rules for predicate logic             *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2015                            *)
(* ========================================================================== *)


module type Bool_sig = sig

  (* Syntax functions *)

  val mk_not : term -> term
  val dest_not : term -> term
  val is_not : term -> bool

  val mk_disj : term * term -> term
  val list_mk_disj : term list -> term
  val dest_disj : term -> term * term
  val strip_disj : term -> term list
  val flatstrip_disj : term -> term list
  val is_disj : term -> bool

  val mk_uexists : term * term -> term
  val dest_uexists : term -> term * term
  val is_uexists : term -> bool

  val mk_cond : term * term * term -> term
  val dest_cond : term -> term * term * term
  val is_cond : term -> bool

  (* Constants *)

  val false_tm : term

  (* Definitions *)

  val false_def : thm
  val not_def : thm
  val disj_def : thm
  val uexists_def : thm
  val cond_def : thm

  (* Theorems *)

  val truth_thm : thm
  val fun_eq_thm : thm
  val imp_alt_def_thm : thm

  (* Inference rules *)

  val add_asm_rule : term -> thm -> thm
  val choose_rule : term * thm -> thm -> thm
  val conj_rule : thm -> thm -> thm
  val conjunct1_rule : thm -> thm
  val conjunct2_rule : thm -> thm
  val contr_rule : term -> thm -> thm
  val deduct_antisym_rule : thm -> thm -> thm
  val deduct_contrapos_rule : term -> thm -> thm
  val disj1_rule : thm -> term -> thm
  val disj2_rule : term -> thm -> thm
  val disj_cases_rule : thm -> thm -> thm -> thm
  val eq_imp_rule1 : thm -> thm
  val eq_imp_rule2 : thm -> thm
  val eqf_elim_rule : thm -> thm
  val eqf_intro_rule : thm -> thm
  val eqt_elim_rule : thm -> thm
  val eqt_intro_rule : thm -> thm
  val eta_conv : term -> thm
  val gen_rule : term -> thm -> thm
  val list_gen_rule : term list -> thm -> thm
  val imp_antisym_rule : thm -> thm -> thm
  val imp_trans_rule : thm -> thm -> thm
  val list_imp_trans_rule : thm list -> thm
  val not_elim_rule : thm -> thm
  val not_intro_rule : thm -> thm
  val prove_asm_rule : thm -> thm -> thm
  val spec_rule : term -> thm -> thm
  val list_spec_rule : term list -> thm -> thm
  val spec_all_rule : thm -> thm
  val bspec_rule : term -> thm -> thm
  val list_bspec_rule : term list -> thm -> thm
  val eq_sym_conv : term -> thm
  val undisch_rule : thm -> thm

end;;
