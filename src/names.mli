(* ========================================================================== *)
(* NAMES (HOL Zero)                                                           *)
(* - Classification of names for parsing/printing                             *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2011                            *)
(* ========================================================================== *)


module type Names_sig = sig

  type hand = Left | Right

  (* Basic name classes *)

  val is_digit : char -> bool
  val is_lowercase : char -> bool
  val is_uppercase : char -> bool
  val is_letter : char -> bool

  val is_punctuation_char : char -> bool
  val is_whitespace_char : char -> bool
  val is_alphanum_char1 : char -> bool
  val is_alphanum_char2 : char -> bool
  val is_symbolic_char : char -> bool
  val is_unprintable_char : char -> bool

  val is_alphanum : string -> bool
  val is_numeric : string -> bool
  val is_symbolic : string -> bool
  val is_keyword : string -> bool

  (* Enumerations *)

  val set_enum_brackets : string * string -> string * string -> unit
  val get_all_enum_info : unit -> ((string * string) * (string * string)) list
  val get_enum_zero_brackets : string -> string * string
  val get_enum_zero_op : string -> string
  val get_enum_bracket_zero : string -> string
  val is_enum_bracket : string -> bool
  val is_enum_open : string -> bool
  val is_enum_close : string -> bool
  val is_enum_openclose : string -> bool

  (* Fixity datatype *)

  type assochand =
      LeftAssoc
    | RightAssoc
    | NonAssoc

  type fixity =
      Nonfix
    | Prefix
    | Infix of (int * assochand)
    | Postfix
    | Binder

  (* Type fixity *)

  val set_type_fixity : string * fixity -> unit
  val reset_type_fixity : string -> unit
  val get_type_fixity : string -> fixity
  val get_all_type_fixities : unit -> (string * fixity) list

  val get_infix_type_info : string -> int * assochand
  val has_nonfix_type_fixity : string -> bool
  val has_infix_type_fixity : string -> bool

  (* Term fixity *)

  val set_fixity : string * fixity -> unit
  val reset_fixity : string -> unit
  val get_fixity : string -> fixity
  val get_all_fixities : unit -> (string * fixity) list

  val get_infix_info : string -> int * assochand
  val has_nonfix_fixity : string -> bool
  val has_prefix_fixity : string -> bool
  val has_infix_fixity : string -> bool
  val has_postfix_fixity : string -> bool
  val has_binder_fixity : string -> bool

end;;
