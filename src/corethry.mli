(* ========================================================================== *)
(* CORE THEORY (HOL Zero)                                                     *)
(* - A core theory for the HOL logic                                          *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2011                            *)
(* ========================================================================== *)


module type CoreThry_sig = sig

  open Type
  open Term
  open Thm

  (* Type constants *)

  val bool_ty : hol_type

  (* Constants *)

  val true_tm : term

  (* Axioms *)

  val eta_ax : thm
  val imp_antisym_ax : thm
  val select_ax : thm

  (* Definitions *)

  val true_def : thm
  val conj_def : thm
  val forall_def : thm
  val exists_def : thm
  val one_one_def : thm
  val type_definition_def : thm

end;;
