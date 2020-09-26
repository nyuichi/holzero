(* ========================================================================== *)
(* PRETYPES AND PRETERMS (HOL Zero)                                           *)
(* - Intermediate datatypes for types/terms used in parsing and printing      *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2013                            *)
(* ========================================================================== *)


module type Preterm_sig = sig

  open Type
  open Term

  (* Pretypes *)

  type pretype =
      Ptyvar of string
    | Ptygvar of int
    | Ptycomp of (string * pretype list)

  (* Pretype syntax functions *)

  val mk_fun_pretype : pretype * pretype -> pretype
  val dest_fun_pretype : pretype -> pretype * pretype

  val mk_bin_pretype : string * pretype * pretype -> pretype
  val strip_infix_pretype : pretype -> string * pretype list

  val is_gtyvar_pretype : pretype -> bool

  (* Pretype utilities *)

  val type_to_pretype : hol_type -> pretype
  val pretype_to_type : pretype -> hol_type

  val pretype_gtyvars : pretype -> pretype list
  val pretype_has_gtyvars : pretype -> bool

  val pretype_inst : (pretype * pretype) list -> pretype -> pretype
  val pretype_match : pretype * pretype -> (pretype * pretype) list

  val pretype_complexity : pretype -> int

  (* Preterms *)

  type preterm =
      Ptmvar of (string * pretype)
    | Ptmconst of (string * pretype)
    | Ptmcomb of (preterm * preterm)
    | Ptmabs of (preterm * preterm)
    | Ptmtyped of (preterm * pretype)

  (* Preterm syntax functions *)

  val mk_nulltype_var_preterm : string -> preterm
  val dest_var_preterm : preterm -> string * pretype

  val mk_nulltype_const_preterm : string -> preterm
  val const_preterm_name : preterm -> string

  val mk_comb_preterm : preterm * preterm -> preterm
  val list_mk_comb_preterm : preterm * preterm list -> preterm
  val dest_comb_preterm : preterm -> preterm * preterm
  val strip_comb_preterm : preterm -> preterm * (preterm list)

  val list_mk_abs_preterm : preterm list * preterm -> preterm
  val strip_abs_preterm : preterm -> (preterm list) * preterm

  val is_typed_preterm : preterm -> bool

  val atom_preterm_name : preterm -> string
  val is_atom_preterm : preterm -> bool

  val mk_bin_preterm : preterm * preterm * preterm -> preterm
  val dest_bin_preterm : preterm -> preterm * preterm * preterm

  val mk_cond_preterm : preterm * preterm * preterm -> preterm
  val dest_cond_preterm : preterm -> preterm * preterm * preterm
  val is_cond_preterm : preterm -> bool

  val mk_let_preterm : (preterm * preterm) list * preterm -> preterm
  val dest_let_preterm : preterm -> (preterm * preterm) list * preterm
  val is_let_preterm : preterm -> bool

  val list_mk_pair_preterm : preterm list -> preterm
  val strip_pair_preterm : preterm -> preterm list
  val is_pair_preterm : preterm -> bool

  val mk_nat_preterm_big_int : big_int -> preterm
  val dest_nat_preterm_big_int : preterm -> big_int
  val is_nat_preterm : preterm -> bool

  val mk_enum_preterm : string * preterm list * string -> preterm
  val dest_enum_preterm : preterm -> string * preterm list * string
  val is_enum_preterm : preterm -> bool

  val list_mk_binder_preterm : preterm * preterm list * preterm -> preterm
  val strip_infix_preterm : preterm -> preterm * preterm list
  val strip_binder_preterm : preterm -> preterm * preterm list * preterm
  val is_prefix_preterm : preterm -> bool
  val is_infix_preterm : preterm -> bool
  val is_postfix_preterm : preterm -> bool
  val is_binder_preterm : preterm -> bool

  (* Preterm utilities *)

  val term_to_preterm : term -> preterm
  val preterm_to_term : preterm -> term

  val preterm_gtyvars : preterm -> pretype list
  val preterm_has_gtyvars : preterm -> bool

  val preterm_inst : (pretype * pretype) list -> preterm -> preterm
  val preterm_pretype_match : preterm * preterm -> (pretype * pretype) list

end;;
