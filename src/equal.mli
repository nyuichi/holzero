(* ========================================================================== *)
(* EQUALITY (HOL Zero)                                                        *)
(* - Extra theory and derived rules for equality reasoning                    *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2015                            *)
(* ========================================================================== *)


module type Equal_sig = sig

  (* Syntax functions *)

  val mk_let : (term * term) list * term -> term
  val dest_let : term -> (term * term) list * term
  val is_let : term -> bool

  (* Definitions *)

  val let_def : thm
  val onto_def : thm

  (* Inference rules *)

  val mk_comb1_rule : thm -> term -> thm
  val mk_comb2_rule : term -> thm -> thm

  val eq_sym_rule : thm -> thm
  val eq_trans_rule : thm -> thm -> thm
  val list_eq_trans_rule : thm list -> thm

  val alpha_link_conv : term -> term -> thm
  val alpha_conv : term -> term -> thm

  val subs_rule : thm list -> thm -> thm
  val subs_conv : thm list -> term -> thm
  val subst_rule : (term * thm) list -> term -> thm -> thm
  val subst_conv : (term * thm) list -> term -> term -> thm

  val conv_rule : (term -> thm) -> thm -> thm

  val app_beta_rhs_rule : thm -> term -> thm
  val list_app_beta_rhs_rule : thm -> term list -> thm
  val app_beta_rule : thm -> term -> thm
  val list_app_beta_rule : thm -> term list -> thm

end;;
