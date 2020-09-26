(* ========================================================================== *)
(* TYPES (HOL Zero)                                                           *)
(* - Datatype for internal types plus support for type constant declaration   *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2012                            *)
(* ========================================================================== *)


module type Type_sig = sig

  (* Type datatype *)

  type hol_type

  (* Primitive syntax functions *)

  val mk_var_type : string -> hol_type
  val dest_var_type : hol_type -> string
  val is_var_type : hol_type -> bool

  val mk_comp_type : string * hol_type list -> hol_type
  val dest_comp_type : hol_type -> string * hol_type list
  val is_comp_type : hol_type -> bool

  (* Primitive type constant declaration *)

  val prim_new_tyconst : string * big_int -> unit
  val prim_get_tyconst_arity : string -> big_int
  val prim_get_all_tyconsts : unit -> (string * big_int) list
  val is_tyconst_name : string -> bool

  (* Primitive utilities *)

  val type_eq : hol_type -> hol_type -> bool
  val type_lt : hol_type -> hol_type -> bool

  val mk_fun_type : hol_type * hol_type -> hol_type
  val dest_fun_type : hol_type -> hol_type * hol_type
  val is_fun_type : hol_type -> bool

  val type_inst : (hol_type * hol_type) list -> hol_type -> hol_type

end;;
