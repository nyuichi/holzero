(* ========================================================================== *)
(* LEXER (HOL Zero)                                                           *)
(* - Lexer for type and term quotations                                       *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2016                            *)
(* ========================================================================== *)


module Lexer : Lexer_sig = struct


(* This module implements the lexical analysis stage, common to both HOL type *)
(* and term quotation parsing.  The syntax and top-level parsers for types    *)
(* and terms are implemented in the 'Parser' module.  The classification of   *)
(* characters, used to determine how lexical tokens are formed, is            *)
(* implemented in the 'Names' module.                                         *)

(* The lexer is implemented as a recursive descent parser, written using      *)
(* lexical reader functions and reader combinators to transparently reflect   *)
(* the formal grammar.  The reader combinators are implemented in the         *)
(* 'Reader' module.                                                           *)


open Reader;;
open Names;;



(* ** LEXER UTILITIES ** *)


(* Specialised lexical reader combinators *)

(* These specialise the reader combinators for use on a character list        *)
(* source.                                                                    *)

let lex_char_with =
  (read_elem_with : (char -> bool) -> (char list, char) reader);;

let lex_char_in =
  (read_elem_in : char list -> (char list, char) reader);;

let lex_char_not_in =
  (read_elem_not_in : char list -> (char list, char) reader);;

let lex_list =
  (read_list : int -> (char list, 'a) reader -> (char list, 'a list) reader);;

let lex_end =
  (read_end : (char list, unit) reader);;


(* Error handling *)

let lex_error x = hol_error ("LEXICAL ERROR", x);;

let ( /+ ) read_fn msg src =
  try  read_fn src
  with ReadFail -> lex_error msg;;



(* ** LEXICAL TOKEN DATATYPE ** *)

(* The lexical syntax for type and term quotations consists of three basic    *)
(* classes:                                                                   *)
(*  Identifiers - for referring to names of entities;                         *)
(*  Numerics - in types: an extra form of identifier, in terms: numerals;     *)
(*  Reserved words - for syntactic sugar.                                     *)

(* Identifiers optionally carry special markings to disambiguate what they    *)
(* are referring to.  White space can be used to separate tokens, and isn't   *)
(* recorded in tokens.                                                        *)


(* Datatype definition *)

type varmark = Tyvar_mark | Tmvar_mark | No_mark;;

type token =
   Ident_tok of (bool * varmark * string)
 | Numeric_tok of (bool * varmark * string)
 | Resword_tok of string;;


(* Token name *)

let token_name tok =
  match tok with
    Ident_tok (_,_,x)   -> x
  | Numeric_tok (_,_,x) -> x
  | Resword_tok x       -> x;;



(* ** LEXICAL ANALYSIS ** *)

(* The lexical reader functions operate on a list of characters for their     *)
(* source, reading off characters from the front of the list and grouping     *)
(* them into strings that are used to form lexical tokens.  The lexer outputs *)
(* a list of lexical tokens.                                                  *)

(* Normally, entities will have an alphanumeric or symbolic name that doesn't *)
(* clash with a reserved word, and will simply be referred to by their name.  *)
(* For entity names that are irregular or that clash with a reserved word,    *)
(* double-quote delimiters must be put around the name to disambiguate (with  *)
(* any backslash, double-quote, backquote or unprintable characters in the    *)
(* name backslash-escaped).  Such a device helps achieve parser completeness  *)
(* and printer soundness, by allowing entities to have any name without       *)
(* causing ambiguity.                                                         *)

(* Identifiers can have special markings immediately before their core name,  *)
(* to show that they refer to a particular form of entity.  A "'" mark refers *)
(* to a tyvar, and a "%" mark refers to a var.  This, again, helps achieve    *)
(* parser completeness and printer soundness, by allowing tyvars and vars     *)
(* respectively to have names of constants and type constants without causing *)
(* ambiguity.  An identifier can also be "defixed" (i.e. released from the    *)
(* fixity of its name and given nonfix status) with a "$" mark (coming before *)
(* any "'" or "%" mark).  This allows entities with fixity to occur without   *)
(* arguments.                                                                 *)


(* Token lexer *)

(* A lexical token can be an identifier, a numeric or a reserved word.        *)
(* Numerics and identifiers may have marks to distinguish their status.       *)
(*                                                                            *)
(* alphanum   =  Alphanum_char1 { Alphanum_char2 }*                           *)
(*                                                                            *)
(* symbolic   =  { Symbolic_char }+                                           *)
(*                                                                            *)
(* quote      =  Dquote                                                       *)
(*                 { Normal_char                                              *)
(*                 | Backslash ( Backslash | Dquote | Digit Digit Digit ) }*  *)
(*               Dquote                                                       *)
(*                                                                            *)
(* ident      =  { "$" }? { "'" | "%" }? ( alphanum | symbolic | quote )      *)
(*                                                                            *)
(* numeric    =  { "$" }? { "'" }? Digit { Digit | "_" }*                     *)
(*                                                                            *)
(* resword    =  Punctuation | Keyword | Enumbrkt                             *)
(*                                                                            *)
(* token      =  ident | numeric | resword                                    *)

let rec lex_token0 (dfx,vmrk) =
  (* Punctuation *)
  (fun c -> let x = char_implode [c] in
            if dfx || not (vmrk = No_mark)
              then lex_error ("Cannot mark reserved word " ^ quote x)
              else Resword_tok x) @:
     (lex_char_with is_punctuation_char)
  |||
  (* Alphanumeric *)
  (fun (c,cs) ->
            let x = char_implode (c::cs) in
            if (is_keyword x) || (is_enum_bracket x)
              then if dfx || not (vmrk = No_mark)
                     then lex_error ("Cannot mark reserved word " ^ quote x)
                     else Resword_tok x
              else Ident_tok (dfx,vmrk,x)) @:
     (lex_char_with is_alphanum_char1
      >>>
      lex_list 0 (lex_char_with is_alphanum_char2))
  |||
  (* Numeric *)
  (fun (c,cs) ->
            let x = char_implode (c::cs) in
            if not (is_numeric x)
              then lex_error "Non-numeric character in numeric token"
            else if (vmrk = Tmvar_mark)
              then lex_error "Cannot mark numeric with '%'"
              else Numeric_tok (dfx,vmrk,x)) @:
     (lex_char_with is_digit
      >>>
      lex_list 0 (lex_char_with is_alphanum_char2))
  |||
  (* Symbolic *)
  (fun cs -> let x = char_implode cs in
             if (is_keyword x) || (is_enum_bracket x)
               then if dfx || not (vmrk = No_mark)
                      then lex_error ("Cannot mark reserved word " ^ quote x)
                      else Resword_tok x
               else Ident_tok (dfx,vmrk,x)) @:
     (lex_list 1 (lex_char_with is_symbolic_char))
  |||
  (* Quote *)
  (fun cs -> let x = char_implode cs in
             Ident_tok (dfx,vmrk,x)) @:
     (lex_char_in ['"']
      *>>
      lex_list 0
        ((* Regular characters *)
         lex_char_not_in ['\\'; '"']
         |||
         (* Escape sequence *)
         (lex_char_in ['\\']
          *>> ((* Escaped backslash or double-quote *)
               lex_char_in ['\\'; '"']
               |||
               (* Escape code - three decimal digits between 000 and 255 *)
               (fun ((c1,c2),c3) ->
                     let n = (int_of_string <* char_implode) [c1;c2;c3] in
                     if (n > 255)
                       then lex_error "Character escape code out of range - \
                                       must be 000 to 255"
                       else Char.chr n) @:
                 ((lex_char_with is_digit
                          /+ "Invalid escape character - must be '\\', '\"' \
                              or ASCII code")
                  >>> (lex_char_with is_digit
                          /+ "Missing escape code digits - must be 3 digits")
                  >>> (lex_char_with is_digit
                          /+ "Missing escape code digit - must be 3 digits")))))
      >>* (lex_char_in ['"']  /+  "Missing closing '\"'"))
  |||
  (* Defix mark *)
  (lex_char_in ['$']
   *>> if not (vmrk = No_mark)
         then fun _ -> lex_error "Defixing mark ($) must precede any var mark \
                                  (' or %) in token"
       else if dfx
         then fun _ -> lex_error "Defixing mark ($) cannot be repeated in token"
         else lex_token0 (true,vmrk))
  |||
  (* Term/type var mark *)
  (lex_char_in ['\'';'%']
   *@> (fun c ->
       if not (vmrk = No_mark)
         then fun _ -> lex_error "Cannot have more than one var mark (' or %) \
                                  in token"
         else let vmrk' = if (c = '%') then Tmvar_mark
                                       else Tyvar_mark in
              lex_token0 (dfx,vmrk')))
  |||
  (* Remaining error cases *)
  if dfx
    then fun _ -> lex_error "Defix mark ($) must immediately precede name, \
                             without space"
  else if not (vmrk = No_mark)
    then fun _ -> lex_error "Var marks (' or %) must immediately precede name, \
                             without space"
    else lex_char_with
               (fun c -> (is_unprintable_char c) && not (is_whitespace_char c))
         *@> fun c _ ->
               let n = Char.code c in
               lex_error ("Unprintable ASCII character " ^ string_of_int n ^
                          " - use ASCII escape code inside quotes");;

let lex_token = lex_token0 (false,No_mark);;


(* White space *)

(* Reads 0 or more white space chars.                                         *)

let lex_whitespace =
  lex_list 0 (lex_char_with is_whitespace_char);;


(* Top-level lexer *)

let lex src = fst (try (
  lex_list 0 (lex_token >>* lex_whitespace)
  >>* lex_end
) src
with ReadFail -> lex_error "Undiagnosed lexical error");;


end;;
