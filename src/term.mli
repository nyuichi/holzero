(* ========================================================================== *)
(* TERMS (HOL Zero)                                                           *)
(* - Datatype for internal terms plus support for constant declaration        *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2011                            *)
(* ========================================================================== *)


module type Term_sig = sig

  open Type

  (* Term datatype *)

  type term

  (* Primitive syntax functions *)

  val mk_var : string * hol_type -> term
  val dest_var : term -> string * hol_type
  val is_var : term -> bool

  val mk_gconst : string -> term
  val mk_iconst : string * (hol_type * hol_type) list -> term
  val dest_const : term -> string * hol_type
  val is_const : term -> bool

  val mk_comb : term * term -> term
  val dest_comb : term -> term * term
  val is_comb : term -> bool

  val mk_abs : term * term -> term
  val dest_abs : term -> term * term
  val is_abs : term -> bool

  (* Primitive constant declaration *)

  val prim_new_const : string * hol_type -> unit
  val get_const_gtype : string -> hol_type
  val get_all_consts : unit -> (string * hol_type) list
  val is_const_name : string -> bool

  (* Primitive utilities *)

  val term_eq : term -> term -> bool
  val term_lt : term -> term -> bool

  val type_of : term -> hol_type

end;;
