(* ========================================================================== *)
(* INFERENCE KERNEL (HOL Zero)                                                *)
(* - Datatype for internal theorems plus primitive inference and assertion    *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2015                            *)
(* ========================================================================== *)


module type Thm_sig = sig

  open Type
  open Term

  (* Theorem datatype *)

  type thm

  val dest_thm : thm -> term list * term
  val asms : thm -> term list
  val concl : thm -> term

  val thm_eq : thm -> thm -> bool

  (* Primitive inference rules *)

  val prim_eq_refl_conv : term -> thm
  val prim_beta_conv : term -> thm

  val prim_mk_comb_rule : thm -> thm -> thm
  val prim_mk_abs_rule : term -> thm -> thm

  val prim_assume_rule : term -> thm
  val prim_disch_rule : term -> thm -> thm
  val prim_mp_rule : thm -> thm -> thm
  val prim_eq_mp_rule : thm -> thm -> thm

  val prim_inst_rule : (term * term) list -> thm -> thm
  val prim_inst_type_rule : (hol_type * hol_type) list -> thm -> thm

  (* Primitive assertion commands *)

  val prim_new_axiom : string * term -> thm
  val get_axiom : string -> thm
  val get_all_axioms : unit -> (string * thm) list

  val prim_new_const_definition : string * term -> thm
  val get_const_definition : string -> thm
  val get_all_const_definitions : unit -> (string * thm) list

  val prim_new_const_specification : string list * thm -> thm
  val get_const_specification : string -> thm
  val get_const_specification_info : string -> (string list * thm) * thm
  val get_all_const_specifications : unit -> (string list * thm) list
  val get_all_const_specification_info :
                                   unit -> ((string list * thm) * thm) list

  val prim_new_tyconst_definition : string * thm -> thm
  val get_tyconst_definition : string -> thm
  val get_tyconst_definition_info : string -> thm * thm
  val get_all_tyconst_definitions : unit -> (string * thm) list
  val get_all_tyconst_definition_info : unit -> (string * (thm * thm)) list

end;;
