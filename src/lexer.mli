(* ========================================================================== *)
(* LEXER (HOL Zero)                                                           *)
(* - Lexer for type and term quotations                                       *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2010                            *)
(* ========================================================================== *)


module type Lexer_sig = sig

  type varmark = Tyvar_mark | Tmvar_mark | No_mark

  type token =
     Ident_tok of (bool * varmark * string)
   | Numeric_tok of (bool * varmark * string)
   | Resword_tok of string

  val token_name : token -> string

  val lex : char list -> token list

end;;
