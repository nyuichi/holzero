(* ========================================================================== *)
(* BASIC UTILITIES II (HOL Zero)                                              *)
(* - More basic derived operations on types, terms and theorems               *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2015                            *)
(* ========================================================================== *)


module type Utils2_sig = sig

  open Type
  open Term
  open Thm

  (* Type syntax functions *)

  val list_mk_fun_type : hol_type list * hol_type -> hol_type
  val strip_fun_type : hol_type -> hol_type list * hol_type

  (* Term syntax functions *)

  val is_cbin : string -> term -> bool
  val is_cbinder : string -> term -> bool

  val rator : term -> term
  val rand : term -> term
  val strip_comb : term -> term * term list

  val list_mk_abs : term list * term -> term
  val bvar : term -> term
  val body : term -> term
  val strip_abs : term -> term list * term

  val eq_lhs : term -> term
  val eq_rhs : term -> term

  val list_mk_imp : term list * term -> term
  val strip_imp : term -> term list * term

  val mk_conj : term * term -> term
  val list_mk_conj : term list -> term
  val dest_conj : term -> term * term
  val strip_conj : term -> term list
  val flatstrip_conj : term -> term list
  val is_conj : term -> bool

  val mk_forall : term * term -> term
  val list_mk_forall : term list * term -> term
  val dest_forall : term -> term * term
  val strip_forall : term -> term list * term
  val is_forall : term -> bool

  val mk_select : term * term -> term
  val dest_select : term -> term * term
  val is_select : term -> bool

  (* Term utilities *)

  val genvar : hol_type -> term
  val list_variant : term list -> term list -> term list
  val list_cvariant : term list -> term list -> term list

  val list_free_vars : term list -> term list
  val term_free_in : term -> term -> bool
  val all_vars : term -> term list
  val list_all_vars : term list -> term list

  val subst : (term * term) list -> term -> term
  val var_match : term -> term -> (term * term) list
  val term_match : term -> term ->
                               (term * term) list * (hol_type * hol_type) list

  val term_union : term list -> term list -> term list
  val same_types : term -> term -> bool
  val rename_bvar : string -> term -> term
  val find_subterm : (term -> bool) -> term -> term
  val find_subterms : (term -> bool) -> term -> term list

  (* Theorem syntax functions *)

  val dest_eqthm : thm -> term * term
  val eqthm_lhs : thm -> term
  val eqthm_rhs : thm -> term
  val is_eqthm : thm -> bool

  (* Theorem utilities *)

  val thm_free_vars : thm -> term list
  val thm_alpha_eq : thm -> thm -> bool

end;;
