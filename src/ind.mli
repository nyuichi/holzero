(* ========================================================================== *)
(* INDIVIDUALS (HOL Zero)                                                     *)
(* - Theory asserting the existence of an infinite type                       *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2011                            *)
(* ========================================================================== *)


module type Ind_sig = sig

  (* Type constants *)

  val ind_ty : hol_type

  (* Constants *)

  val ind_zero_tm : term
  val ind_suc_fn : term

  (* Axioms *)

  val infinity_ax : thm

  (* Definitions *)

  val ind_suc_zero_spec : thm

  (* Theorems *)

  val ind_suc_not_zero_thm : thm
  val ind_suc_injective_thm : thm

end;;
