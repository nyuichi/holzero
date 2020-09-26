(* ========================================================================== *)
(* NATURAL NUMBER EVALUATION (HOL Zero)                                       *)
(* - Conversions for evaluating natural numeral arithmetic                    *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2010-2011                            *)
(* ========================================================================== *)


module type NatEval_sig = sig

  (* Evaluation conversions *)

  val eval_suc_conv : term -> thm
  val eval_pre_conv : term -> thm
  val eval_add_conv : term -> thm
  val eval_sub_conv : term -> thm
  val eval_mult_conv : term -> thm
  val eval_exp_conv : term -> thm
  val eval_even_conv : term -> thm
  val eval_odd_conv : term -> thm

  val eval_nat_eq_conv : term -> thm
  val eval_lt_conv : term -> thm
  val eval_le_conv : term -> thm
  val eval_gt_conv : term -> thm
  val eval_ge_conv : term -> thm

end;;

