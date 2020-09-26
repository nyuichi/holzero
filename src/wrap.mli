(* ========================================================================== *)
(* INFERENCE KERNEL WRAPPERS (HOL Zero)                                       *)
(* - Basic wrappers for the primitive inference rules and theory commands     *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2010-2015                            *)
(* ========================================================================== *)


module type Wrap_sig = sig

  open Type
  open Term
  open Thm

  (* Inference rules *)

  val eq_refl_conv : term -> thm
  val beta_conv : term -> thm

  val mk_comb_rule : thm -> thm -> thm
  val mk_abs_rule : term -> thm -> thm

  val assume_rule : term -> thm
  val disch_rule : term -> thm -> thm
  val mp_rule : thm -> thm -> thm
  val eq_mp_rule : thm -> thm -> thm

  val inst_rule : (term * term) list -> thm -> thm
  val inst_type_rule : (hol_type * hol_type) list -> thm -> thm

  (* Theory commands *)

  val get_tyconst_arity : string -> int
  val get_all_tyconsts : unit -> (string * int) list

  val new_tyconst : string * int -> hol_type
  val new_const : string * hol_type -> term

  val new_axiom : string * term -> thm
  val new_const_definition : term -> thm
  val new_const_specification : string list * thm -> thm
  val new_tyconst_definition : string * thm -> thm

  (* Inference step counting *)

  val step_total : unit -> int
  val step_counter : unit -> int
  val reset_step_counter : unit -> unit

end;;
