(* ========================================================================== *)
(* PARSER (HOL Zero)                                                          *)
(* - Syntax and top-level parsers for type and term quotations                *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2011                            *)
(* ========================================================================== *)


module type Parser_sig = sig

  open Type
  open Term

  (* Parsers *)

  val parse_type : string -> hol_type
  val parse_term : string -> term

  (* Quotation expander *)

  val expand_hol_quotation : string -> string

end;;
