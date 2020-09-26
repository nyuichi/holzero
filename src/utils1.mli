(* ========================================================================== *)
(* BASIC UTILITIES I (HOL Zero)                                               *)
(* - Essential basic derived operations on types and terms                    *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2011                            *)
(* ========================================================================== *)


module type Utils1_sig = sig

  open Type
  open Term

  (* Type syntax functions *)

  type destructed_type =
        Type_var of string
      | Type_comp of (string * hol_type list)
  val dest_type : hol_type -> destructed_type

  val is_bool_type : hol_type -> bool

  val a_ty : hol_type
  val b_ty : hol_type
  val c_ty : hol_type

  (* Type utilities *)

  val type_tyvars : hol_type -> hol_type list
  val type_match0 : (hol_type * hol_type) list
                         -> hol_type -> hol_type -> (hol_type * hol_type) list
  val type_match : hol_type -> hol_type -> (hol_type * hol_type) list

  (* Term syntax functions *)

  type destructed_term =
        Term_var of (string * hol_type)
      | Term_const of (string * hol_type)
      | Term_comb of (term * term)
      | Term_abs of (term * term)
  val dest_term : term -> destructed_term

  val var_name : term -> string
  val var_type : term -> hol_type

  val mk_const : string * hol_type -> term
  val const_name : term -> string
  val const_type : term -> hol_type

  val list_mk_comb : term * term list -> term

  val mk_bin : term * term * term -> term
  val dest_bin : term -> term * term * term
  val dest_cbin : string -> term -> term * term
  val is_bin : term -> bool

  val mk_binder : term * term * term -> term
  val dest_binder : term -> term * term * term
  val dest_cbinder : string -> term -> term * term
  val is_binder : term -> bool

  val is_bool_term : term -> bool

  val mk_eq : term * term -> term
  val dest_eq : term -> term * term
  val is_eq : term -> bool

  val mk_imp : term * term -> term
  val dest_imp : term -> term * term
  val is_imp : term -> bool

  val mk_exists : term * term -> term
  val list_mk_exists : term list * term -> term
  val dest_exists : term -> term * term
  val strip_exists : term -> term list * term
  val is_exists : term -> bool

  (* Term utilities *)

  val term_tyvars : term -> hol_type list

  val alpha_eq : term -> term -> bool

  val free_vars : term -> term list
  val var_free_in : term -> term -> bool

  val variant : term list -> term -> term
  val cvariant : term list -> term -> term

  val tyvar_inst : (hol_type * hol_type) list -> term -> term
  val var_inst : (term * term) list -> term -> term

end;;
