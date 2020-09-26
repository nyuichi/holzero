(* ========================================================================== *)
(* PARSER (HOL Zero)                                                          *)
(* - Syntax and top-level parsers for type and term quotations                *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2016                            *)
(* ========================================================================== *)


module Parser : Parser_sig = struct


(* This module implements syntax analysis and top-level parsing of type/term  *)
(* quotations into internal types/terms.  The syntax parsers take a list of   *)
(* lexical tokens as their source, and return a pretype/preterm that gets     *)
(* passed on to type analysis.  Lexical analysis is implemented in the        *)
(* 'Lexer' module, and type analsyis (actually common to parsing and          *)
(* printing) is implemented in the 'TypeAnal' module.                         *)

(* The syntax parsers are implemented as recursive descent parsers, written   *)
(* using syntax reader functions and reader combinators to transparently      *)
(* reflect the formal grammar.  The reader combinators are implemented in the *)
(* 'Reader' module.                                                           *)

(* The parsers have two important parser soundness/completeness properties.   *)
(* Firstly, every well-formed type/term has a quotation representation that   *)
(* can be parsed.  This means the user always has the choice of whether to    *)
(* create an internal expression by supplying a quotation or by using syntax  *)
(* constructor functions.  Secondly, anything outputted by the type/term      *)
(* printers can be parsed to result in an identical internal type/term.  This *)
(* means that printed output can always be simply pasted back for input if    *)
(* required.                                                                  *)

(* Note that these syntax parsers take into account certain specially-        *)
(* supported constants, whose declarations in later modules are anticipated   *)
(* here.                                                                      *)


open Type;;
open Term;;

open Reader;;
open Lexer;;
open Names;;
open Preterm;;
open TypeAnal;;



(* ** LOW-LEVEL SYNTAX ANALYSIS UTILITIES ** *)

(* The syntax reader functions operate on a list of lexical tokens for their  *)
(* source, reading off tokens from the front of the list.  This section       *)
(* defines the low-level utilities to be used with such reader functions.     *)


(* Reserved words tests *)

let is_resword_token tok =
  match tok with
    Resword_tok _ -> true
  | _             -> false;;

let is_eqkwd_token tok =
  match tok with
    Ident_tok (false, No_mark, "=") -> true
  | _                               -> false;;

let is_resword_token_with p tok =
  ((is_resword_token tok)  || (is_eqkwd_token tok)) && p (token_name tok);;

let is_resword_token_in xs0 tok =
  ((is_resword_token tok) || (is_eqkwd_token tok)) &&
  (mem (token_name tok) xs0);;

let is_resword_token_not_in xs0 tok =
  (is_resword_token tok) && not (mem (token_name tok) xs0);;


(* Type token tests *)

let is_nonfix_tyconst_token tok =
  match tok with
    Ident_tok (dfx, No_mark, x) | Numeric_tok (dfx, No_mark, x)
       -> (dfx || (has_nonfix_type_fixity x)) && (is_tyconst_name x)
  | _  -> false;;

let is_infix_tyconst_token tok =
  match tok with
    Ident_tok (dfx, No_mark, x) | Numeric_tok (dfx, No_mark, x)
       -> (not dfx) && (has_infix_type_fixity x) && (is_tyconst_name x)
  | _  -> false;;

let is_tyvar_token tok =
  match tok with
    Ident_tok (_, vmrk, x) | Numeric_tok (_, vmrk, x)
       -> (vmrk = Tyvar_mark) || ((vmrk = No_mark) && not (is_tyconst_name x))
  | _  -> false;;


(* Term token tests *)

let is_nonfix_token tok =
  match tok with
    Ident_tok (dfx, (Tmvar_mark|No_mark), x)
       -> dfx || (has_nonfix_fixity x)
  | _  -> false;;

let is_prefix_token tok =
  match tok with
    Ident_tok (dfx, (Tmvar_mark|No_mark), x)
       -> (not dfx) && (has_prefix_fixity x)
  | _  -> false;;

let is_infix_token tok =
  match tok with
    Ident_tok (dfx, (Tmvar_mark|No_mark), x)
       -> (not dfx) && (has_infix_fixity x)
  | _  -> false;;

let is_postfix_token tok =
  match tok with
    Ident_tok (dfx, (Tmvar_mark|No_mark), x)
       -> (not dfx) && (has_postfix_fixity x)
  | _  -> false;;

let is_binder_token tok =
  match tok with
    Ident_tok (dfx, (Tmvar_mark|No_mark), x)
       -> (not dfx) && (has_binder_fixity x)
  | _  -> false;;

let is_var_token tok =
  match tok with
    Ident_tok (_, vmrk, x)
       -> (vmrk = Tmvar_mark) || ((vmrk = No_mark) && not (is_const_name x))
  | _  -> false;;

let is_const_token tok =
  match tok with
    Ident_tok (_,vmrk,x)
       -> (vmrk = No_mark) && (is_const_name x)
  | _  -> false;;

let is_nonfix_var_token tok = (is_var_token tok) && (is_nonfix_token tok);;

let is_numeral_token tok =
  match tok with
    Numeric_tok (_,vmrk,_) -> (vmrk = No_mark)
  | _                      -> false;;


(* Specialised syntax reader combinators *)

(* These specialise the reader combinators for use a token list source.       *)

let parse_list =
  (read_list : int -> (token list, 'a) reader -> (token list, 'a list) reader);;

let parse_start =
  (read_start : (token list, unit) reader);;

let parse_end =
  (read_end : (token list, unit) reader);;

let parse_equals_kwd =
  token_name @:
     read_elem_with is_eqkwd_token;;

let parse_name_with test_fn =
  token_name @:
     read_elem_with test_fn;;

let parse_resword x = parse_name_with (is_resword_token_in [x]);;

let parse_resword_in xs = parse_name_with (is_resword_token_in xs);;

let parse_resword_not_in xs = parse_name_with (is_resword_token_not_in xs);;



(* ** SYNTAX ERROR SUPPORT ** *)

(* This section defines the support for the detection and raising of syntax   *)
(* errors (as HolError exceptions).  Syntax errors carry a diagnosis message  *)
(* that pins down the cause of an error.  An "Undiagnosed" message is raised  *)
(* as a "catch-all" at the top level if no specific cause can be found.       *)


(* Error raising function *)

let syntax_error x = hol_error ("SYNTAX ERROR", x);;


(* Error combinators *)

(* The mechanism for detecting/raising syntax errors involves use of a        *)
(* dedicated combinator - either '/!' or '//!'.  These take a syntax reader   *)
(* function as their LHS, for reading syntax-correct expressions.  If the     *)
(* reader function raises a ReadFail exception, then the RHS takes over to    *)
(* determine what action to take, potentially raising a syntax error.         *)

(* For '/!', the RHS is simply a string that becomes a syntax error diagnosis *)
(* message.                                                                   *)

let ( /! ) parse_fn msg src =
  try  parse_fn src
  with ReadFail -> syntax_error msg;;

(* For '//!', the RHS is a diagnosis function.  Diagnosis functions examine   *)
(* the source and either return a diagnosis message string (for when an error *)
(* has certainly been found) or raise a ReadFail (for when it is uncertain,   *)
(* because other branches of the grammar have not yet been explored).  If a   *)
(* string is returned, it gets used as the diagnosis message for a syntax     *)
(* error.                                                                     *)

let ( //! ) parse_fn err_fn =
   parse_fn
   |||
   syntax_error @: (fun src -> (err_fn src, src));;


(* Utility *)

let ored items =
  foldr1 (fun item1 item2 () -> item1 () ^ " or " ^ item2 ()) items;;


(* Diagnosis functions *)

(* Various diagnosis functions are defined here for detecting specific syntax *)
(* error scenarios.  As well as its source argument (as its last arg), a      *)
(* diagnosis function may take reserved word arg(s) (with name 'rw(s)') that  *)
(* get used in the diagnosis test and/or the diagnosis message, and may also  *)
(* take context arg(s) (with name 'item(s)') for portraying additional        *)
(* information in the diagnosis message.  Syntax reader functions are used to *)
(* perform the diagnosis tests, but in such a way that a syntax error is      *)
(* raised if the reader succeeds (and ReadFail is assumed to be raised by the *)
(* reader itself if it fails).                                                *)

(* Context args come as functions that take unit and return a string, rather  *)
(* than simply as strings.  This is to delay construction of the diagnosis    *)
(* message until a syntax error has actually been detected, thus saving on    *)
(* unnecessary string construction for potential syntax errors that don't     *)
(* materialise.                                                               *)


(* This checks that there are still tokens left to parse.                     *)

let end_of_qtn_err items =
  (fun _ -> "Unexpected end of quotation instead of " ^ ored items ()) @!:
     parse_end;;


(* This checks that the next token isn't a resword that should occur later.   *)

let early_resword_err rws item =
  (fun _ -> "Missing " ^ item ()) @!:
     parse_resword_in rws;;


(* These check that the next token isn't a resword not in 'rws'.              *)

let hit_resword_err rws context =
  (fun x -> "Unexpected reserved word " ^ quote x ^ " " ^ context ()) @!:
     parse_resword_not_in rws;;

let hit_resword_instead_err rws items =
  hit_resword_err rws (fun()-> "instead of " ^ ored items ());;

let wrong_resword_err rws =
  hit_resword_instead_err rws (map (fun rw () -> quote rw) rws);;


(* This checks that eventually there's a closing reserved word 'rw2'.         *)

let rec no_close_err0 n (rw1,rw2) src = (
  if (n = 0)
    then (fun src -> raise ReadFail)
    else parse_list 0 (parse_resword_not_in [rw1;rw2])
         *>> ((parse_resword rw1 *>> no_close_err0 (n+1) (rw1,rw2))
              |||
              (parse_resword rw2 *>> no_close_err0 (n-1) (rw1,rw2))
              |||
              parse_end)
) src;;

let no_close_err (rw1,rw2) =
  (fun _ -> "Opening " ^ quote rw1 ^ " but no subsequent " ^ quote rw2) @!:
     no_close_err0 1 (rw1,rw2);;


(* Leading reserved words *)

(* This is a list of reserved words that do not require a preceeding reserved *)
(* word in a quotation.  This is used to help error detection in some         *)
(* situations.                                                                *)

let leading_type_reswords = ["("];;

let leading_term_reswords () =
  ["("; "\\"; "if"; "let"; ":"] @
  (map (fst <* snd) (get_all_enum_info ()));;



(* ** HIGH-LEVEL SYNTAX ANALYSIS UTILITIES ** *)

(* This section provides support for specific syntactic forms, in particular  *)
(* for calling the appropriate error diagnosis functions for the form.  The   *)
(* forms are broken into 5 classes (A to D and infix).                        *)


(* The A-class is for "mixfix middle" items, that occur immediately proceeded *)
(* by a reserved word from the list 'rws'.                                    *)

let parse_itemA item rws parse_fn =
  parse_fn           //! end_of_qtn_err [item]
                     //! early_resword_err rws item
                     //! hit_resword_instead_err rws [item];;

let parse_reswordA rw =
  parse_resword rw   //! end_of_qtn_err [fun()-> quote rw]
                     //! wrong_resword_err [rw];;

let parse_listA item rw parse_fn1 =
  let items = [item; fun () -> quote rw] in
  (fun (x,xs) -> x::xs) @:
     (parse_itemA item [rw] (parse_fn1 [item])
      >>> parse_list 0 (parse_fn1 items)
      >>* (parse_resword "."    //! end_of_qtn_err items
                                //! hit_resword_instead_err [rw] items));;


(* The B-class is for "mixfix tail" items, that have no trailing reserved     *)
(* word.                                                                      *)

let parse_itemB item parse_fn =
  parse_fn          //! end_of_qtn_err [item]
                    //! hit_resword_instead_err [] [item];;


(* The C-class is for "bracketed" items, that occur immediately proceeded by  *)
(* given closing bracket 'br2' that corresponds to an earlier opening bracket *)
(* 'br1'.                                                                     *)

let parse_itemC item (br1,br2) parse_fn =
  parse_fn          //! no_close_err (br1,br2)
                    //! early_resword_err [br2] item
                    //! hit_resword_instead_err [br2] [item];;


(* The D-class is for items that occur in sequence, separated by given        *)
(* reserved word 'sep' and surrounded by given bracket reserved words 'br1'   *)
(* and 'br2'.                                                                 *)

let parse_itemD item (br1,sep,br2) parse_fn =
  parse_fn          //! no_close_err (br1,br2)
                    //! early_resword_err [sep;br2] item
                    //! hit_resword_instead_err [sep;br2] [item];;

let parse_reswordD (br1,sep,br2) x =
  parse_resword x   //! no_close_err (br1,br2)
                    //! wrong_resword_err [sep;br2];;

(* This is for parsing a variable-length sequences of items, with minimum     *)
(* length 'n', each item separated by resword 'sep' and the sequence          *)
(* delimited at start and end by 'br1' and 'br2' respectively.                *)

let parse_listD0 n item (br1,sep,br2) parse_fn =
  (fun xs -> if (length xs < n) then syntax_error ("Missing " ^ item ())
                                else xs) @:
     ((* Empty list *)
      (fun _ -> []) @:
         parse_resword br2
      |||
      (* Non-empty list *)
      (fun (x,xs) -> x::xs) @:
         (parse_itemD item (br1,sep,br2) parse_fn
          >>> parse_list (decrement n)
                 (    parse_reswordD (br1,sep,br2) sep
                  *>> parse_itemD item (br1,sep,br2) parse_fn)
          >>* parse_resword br2));;

let parse_listD n item (br1,sep,br2) parse_fn =
  parse_resword br1
  *>> parse_listD0 n item (br1,sep,br2) parse_fn;;


(* Infix expression parsing *)

(* This is for parsing a compound infix expression (over possibly more than   *)
(* one infix operator), including building the structured representation.     *)

type ('a,'b) infix_elem =
   Infix_op of 'a
 | Infix_arg of 'b;;

let rec build_revpolish_step (form,name_fn) (elems,fnhs) ((f,n,h),expr) =
  let foo (f1,n1,h1) =
         (n < n1) ||
         ((n = n1) &&
          (if (h = NonAssoc)
             then let x = name_fn f1 in
                  syntax_error ("Missing bracket for " ^
                                "non-associative " ^ form ^ " " ^ quote x)
             else (h = LeftAssoc))) in
  let (fnhs1,fnhs2) = cut_while foo fnhs in
  let y = Infix_arg expr in
  let gs1 = map (fun (f,_,_) -> Infix_op f) fnhs1 in
  let elems' = y :: ((rev gs1) @ elems) in
  let fnhs' = (f,n,h)::fnhs2 in
  (elems',fnhs');;

let build_revpolish (form,name_fn) expr0 fexprs =
  let (elems,fnhs) =
            foldl (build_revpolish_step (form,name_fn)) ([Infix_arg expr0],[])
                  fexprs in
  let gs = map (fun (f,_,_) -> Infix_op f) fnhs in
  (rev gs) @ elems;;

let rec build_infix_expr mk_bin_fn ys =
  match ys with
    (Infix_op f)::ys0
       -> let (expr1,ys1) = build_infix_expr mk_bin_fn ys0 in
          let (expr2,ys2) = build_infix_expr mk_bin_fn ys1 in
          (mk_bin_fn (f,expr2,expr1), ys2)
  | (Infix_arg expr)::ys0
       -> (expr,ys0)
  | [] -> internal_error "build_infix_expr";;

let parse_infix_expr0 (form,name_fn) (parse_fn,parse_op_fn) =
  parse_list 1
    (parse_op_fn
     >@> (fun (f1,n1,_) ->
          let item (h,f) = h ^" for " ^ form ^ " " ^ quote (name_fn f) in
          let item1 () = item ("RHS",f1) in
          parse_fn   //! end_of_qtn_err [item1]
                     //! ((fun (f2,n2,_)-> if (n1>=n2)
                                             then "Missing "^item("RHS",f1)
                                             else "Missing "^item("LHS",f2)) @!:
                              parse_op_fn)
                     //! hit_resword_instead_err [] [item1]));;

let parse_infix_expr (form,name_fn) (parse_fn,parse_op_fn,mk_bin_fn) e0 src =
  let (fes,src') = parse_infix_expr0 (form,name_fn) (parse_fn,parse_op_fn)
                                     src in
  let ys = build_revpolish (form,name_fn) e0 fes in
  let (e,ys1) = build_infix_expr mk_bin_fn ys in
  let _ = try assert (is_empty ys1)
          with Assert_failure _ -> internal_error "parse_infix_expr" in
  (e,src');;



(* ** TYPE SYNTAX ANALYSIS ** *)

(* The type syntax parser takes a list of lexical tokens and produces a       *)
(* pretype.  The concrete syntax for types extends beyond the primitive       *)
(* categories to support infix type constants.                                *)


(* type2  =  Tyvar-Ident/Numeric                                              *)
(*         | Nonfix-Tyconst-Ident/Numeric                                     *)
(*         | "(" { type }++-"," ")" Nonfix-Tyconst-Ident/Numeric              *)
(*         | "(" type ")"                                                     *)
(*                                                                            *)
(* type1  =  type2                                                            *)
(*         | type2 { Nonfix-Tyconst-Ident/Numeric }+                          *)
(*                                                                            *)
(* type   =  type1                                                            *)
(*         | type1 { Infix-Tyconst-Ident/Numeric type1 }+                     *)
(*                                                                            *)
(* Binding priority for left/right-recursive cases (tightest first):          *)
(*   nonfix compound types; infix compound types.                             *)

let parse_infix_tyconst =
  (fun x -> let (n,h) = get_infix_type_info x in
            (x,n,h)) @:
      parse_name_with is_infix_tyconst_token;;

let parse_nonfix_tyconst =
  parse_name_with is_nonfix_tyconst_token
    //! ((fun x -> "Unexpected type variable " ^ quote x ^
                   " instead of type constant") @!:
             parse_name_with is_tyvar_token);;

let rec parse_pretype2 src = (
  (* Type variable *)
  (fun x -> Ptyvar x) @:
     parse_name_with is_tyvar_token
  |||
  (* 0-arity compound type *)
  (fun x -> Ptycomp (x,[])) @:
     parse_name_with is_nonfix_tyconst_token
  |||
  (let delims = ("(", ",", ")") in
   parse_resword "("
   *>> parse_itemD (fun()->"subtype") delims
         (parse_pretype0  //! no_close_err ("(",")")
                          //! early_resword_err [","] (fun()->"type parameter"))
   *@> (fun pty ->
       (* Bracketed subtype *)
       (fun _ -> pty) @:
          parse_reswordD delims ")"
       |||
       (* 2+-arity compound type *)
       (fun (ptys,x) -> Ptycomp (x, pty::ptys)) @:
          (parse_reswordD delims ","
           *>> parse_listD0 1 (fun()->"type parameter") delims parse_pretype0
           >>> parse_itemB (fun()->"type constant")
                (parse_nonfix_tyconst //! ((fun x ->"Type constant " ^ quote x ^
                                                    " is not nonfix") @!:
                                    parse_name_with is_infix_tyconst_token)))))
  |||
  (* Error case *)
  (fun x ->
         syntax_error ("Term variable " ^ quote x ^ " encountered in type")) @:
     (parse_name_with (function Ident_tok (_,Tmvar_mark,_)
                         -> true | _ -> false))
) src

and parse_pretype1 src = (
  parse_pretype2
  |@| (* 1-arity compound type *)
      (fun pty ->
      (fun xs -> foldl (fun pty1 x -> Ptycomp (x,[pty1])) pty xs) @:
         parse_list 1 parse_nonfix_tyconst)
) src

and parse_pretype0 src = (
  (parse_pretype1    //! ((fun x ->"Missing LHS for infix type " ^ quote x) @!:
                               parse_name_with is_infix_tyconst_token))
  |@| (* Infix compound type *)
      parse_infix_expr ("infix type",id_fn)
           (parse_pretype1, parse_infix_tyconst, mk_bin_pretype)
) src;;

let parse_pretype src = fst (try (
  (parse_start         /! "Empty type quotation")
  *>> (parse_pretype0  //! hit_resword_err leading_type_reswords
                               (fun()->"at start of type"))
  >>* (parse_end   //! hit_resword_err []
                         (fun()->"after syntax-correct leading subtype"))
) src
with ReadFail -> syntax_error "Undiagnosed type syntax error");;



(* ** TERM SYNTAX ANALYSIS ** *)

(* The term syntax parser takes a list of lexical tokens and produces a       *)
(* preterm.  The concrete syntax for terms extends significantly beyond the   *)
(* primitive categories to include support for:                               *)
(*  - prefix, infix, postfix and binder function application;                 *)
(*  - type-annotated subexpressions;                                          *)
(*  - conditionals, let-expressions, pairs, enumerations and numerals;        *)
(*  - compound structures of lambda abstractions, nonfix/infix/binder         *)
(*   function applications and pairs.                                         *)

(* Each occurrence of a var or a const is given a null generated tyvar at     *)
(* this stage of parsing.  Proper types for these atoms get resolved during   *)
(* type analysis (see 'TypeAnal' module) to result in a preterm suitable for  *)
(* turning into a coherent well-formed term.                                  *)


(* Term atom parser *)

(* atom   =  Var-Ident                                                        *)
(*         | Const-Ident                                                      *)
(*         | "(" atom ":" type ")"                                            *)

let rec parse_atom_with test_fn src = (
  (* Variable *)
  mk_nulltype_var_preterm @:
     parse_name_with (fun tok -> (is_var_token tok) && (test_fn tok))
  |||
  (* Constant *)
  mk_nulltype_const_preterm @:
     parse_name_with (fun tok -> (is_const_token tok) && (test_fn tok))
  |||
  (* Type-annotated atom *)
  (fun (u,pty) -> Ptmtyped (u,pty)) @:
     (parse_resword "("
      *>> (parse_atom_with test_fn
                 //! no_close_err ("(",")")
                 //! early_resword_err [":"] (fun()->"type annotation subterm"))
      >>* parse_resword ":"
      >>> parse_itemC (fun()->"type annotation type") ("(",")") parse_pretype0
      >>* parse_resword ")")
) src;;


(* A few extra diagnosis functions, specialised for terms *)

let hit_prefix_err items =
  (fun ptm -> let x = atom_preterm_name ptm in
            "Unexpected prefix " ^ quote x ^ " instead of " ^ ored items ()) @!:
     parse_atom_with is_prefix_token;;

let hit_infix_err items =
  (fun ptm -> let x = atom_preterm_name ptm in
            "Unexpected infix " ^ quote x ^ " instead of " ^ ored items ()) @!:
     parse_atom_with is_infix_token;;

let hit_numeral_err items =
  (fun x->"Unexpected numeral " ^ quote x ^ " instead of " ^ ored items ()) @!:
     parse_name_with is_numeral_token;;

let hit_const_err eqkwd items =
  (fun x->"Unexpected const " ^ quote x ^ " instead of " ^ ored items ()) @!:
     parse_name_with (fun tok-> is_const_token tok &&
                                not (eqkwd && is_eqkwd_token tok));;


(* Specialised term atom parsers *)

let parse_infix_op =
  (fun f -> let x = atom_preterm_name f in
            let (n,h) = get_infix_info x in
            (f,n,h)) @:
     parse_atom_with is_infix_token;;

let parse_nonfix_var eqkwd items =
  parse_atom_with is_nonfix_var_token
              //! ((fun x -> "Variable " ^ quote x ^ " is not nonfix") @!:
                      parse_name_with is_var_token)
              //! hit_const_err eqkwd items
              //! hit_numeral_err items;;


(* Term syntax parser *)

(* term5  =  Nonfix-atom                                                      *)
(*         | Numeral                                                          *)
(*         | "if" term1 "then" term1 "else" term1                             *)
(*         | "let" { Nonfix-Var-atom "=" term1 }+-"and" "in" term1            *)
(*         | Backslash { Nonfix-Var-atom }+ "." term1                         *)
(*         | Binder-atom { Nonfix-Var-atom }+ "." term1                       *)
(*         | Enumbrkt { term }*-"," Enumbrkt                                  *)
(*         | "(" { term }++-"," ")"                                           *)
(*         | "(" term ")"                                                     *)
(*                                                                            *)
(* term4  =  term5                                                            *)
(*         | { term5 }++                                                      *)
(*                                                                            *)
(* term3  =  term4                                                            *)
(*         | term4 Postfix-atom                                               *)
(*                                                                            *)
(* term2  =  term3                                                            *)
(*         | Prefix-atom term2                                                *)
(*                                                                            *)
(* term1  =  term2                                                            *)
(*         | term2 { Infix-atom term2 }+                                      *)
(*                                                                            *)
(* term   =  term1                                                            *)
(*         | term1 : type                                                     *)
(*                                                                            *)
(* Binding priority for left/right-recursive cases (tightest first):          *)
(*   function application;                                                    *)
(*   postfix application;                                                     *)
(*   prefix application;                                                      *)
(*   infix application;                                                       *)
(*   lambda abstraction/binder application/conditional/let-expression.        *)

let rec parse_preterm5 src = try (
  (* Atom *)
  parse_atom_with is_nonfix_token
  |||
  (* Numeral *)
  (fun x -> let x0 = (char_implode <* filter is_digit <* char_explode) x in
            mk_nat_preterm_big_int (big_int_of_string x0)) @:
     parse_name_with is_numeral_token
  |||
  (* Conditional *)
  (fun ((ptm0,ptm1),ptm2) -> mk_cond_preterm (ptm0,ptm1,ptm2)) @:
     (parse_resword "if"
      *>> parse_itemA (fun()->"conditional condition") ["then"] parse_preterm1
      >>* parse_reswordA "then"
      >>> parse_itemA (fun()->"conditional then-branch") ["else"] parse_preterm1
      >>* parse_reswordA "else"
      >>> parse_itemB (fun()->"conditional else-branch") parse_preterm1)
  |||
  (* Let-expression *)
  (let parse_let_binding_item =
      let item1 = (fun()->"let-binding variable") in
      parse_itemA item1 ["="] (parse_nonfix_var true [item1])
      >>* (let item2 = (fun()->"\"=\"") in
           parse_reswordA "=" //! hit_numeral_err [item2]
                              //! hit_const_err true [item2])
      >>> parse_itemA (fun()->"let-binding RHS") ["and";"in"] parse_preterm1 in
   mk_let_preterm @:
     (parse_resword "let"
      *>> parse_listD0 1 (fun()->"let-expression binding")
             ("let","and","in") parse_let_binding_item
      >>> parse_itemB (fun()->"let-expression body") parse_preterm1))
  |||
  (* Enumeration expression *)
  (lookahead (parse_name_with (is_resword_token_with is_enum_open))
   *@> ( fun br1 ->
       let z = get_enum_bracket_zero br1 in
       let (_,br2) = get_enum_zero_brackets z in
       (fun ptms -> mk_enum_preterm (br1,ptms,br2)) @:
          parse_listD 0 (fun()->"enumeration item") (br1,",",br2)
                      parse_preterm0) )
  |||
  (* Empty enumeration single token (i.e. without separating space) *)
  (fun br12 -> let z = get_enum_bracket_zero br12 in
               let (br1,br2) = get_enum_zero_brackets z in
               mk_enum_preterm (br1,[],br2)) @:
     parse_name_with (is_resword_token_with is_enum_openclose)
  |||
  (* Lambda abstraction *)
  list_mk_abs_preterm @:
     (parse_resword "\\"
      *>> parse_listA (fun()->"lambda binding variable") "."
                (parse_nonfix_var false)
      >>> parse_itemB (fun()->"lambda body") parse_preterm1)
  |||
  (* Binder expression *)
  (fun ((f,vs),ptm0) -> list_mk_binder_preterm (f,vs,ptm0)) @:
     (parse_atom_with is_binder_token
      >>> parse_listA (fun()->"binding variable") "." (parse_nonfix_var false)
      >>> parse_itemB (fun()->"binder body") parse_preterm1)
  |||
  (* Avoid sub-parse for an annotated infix operator (helps error reporting) *)
  (fun _ -> raise LocalFail) @:
     lookahead (parse_atom_with is_infix_token)
  |||
  (let delims = ("(", ",", ")") in
   parse_resword "("
   *>> parse_itemD (fun()->"subexpression") delims
          (parse_preterm0 //! no_close_err ("(",")")
                          //! early_resword_err [","] (fun()->"pair component"))
   *@> (fun x ->
       (* Bracketed subexpression *)
       (fun _ -> x) @:
          parse_reswordD delims ")"
       |||
       (* Pair expression *)
       (fun xs -> list_mk_pair_preterm (x::xs)) @:
          (parse_reswordD delims ","
           *>> parse_listD0 1 (fun()->"pair component") delims
                      parse_preterm0)) )
  |||
  (* Other error cases *)
  (fun x -> syntax_error ("Type variable " ^ quote x ^
                             " encountered outside type annotation")) @:
     parse_name_with
        (function Ident_tok (_,Tyvar_mark,_) | Numeric_tok (_,Tyvar_mark,_)
                     -> true | _ -> false)
) src
with LocalFail -> raise ReadFail

and parse_preterm4 src = (
  parse_preterm5
  |@| (* Curried function application *)
      (fun ptm ->
      (fun ptms -> list_mk_comb_preterm (ptm,ptms)) @:
         parse_list 1
           (parse_preterm5 //! hit_prefix_err [fun()->"as curried fn arg"]))
) src

and parse_preterm3 src = (
  (parse_preterm4  //! ((fun f -> let x = atom_preterm_name f in
                                  "Missing argument for postfix " ^ quote x) @!:
                            parse_atom_with is_postfix_token))
  |@| (* Postfix expression *)
      (fun ptm ->
      (fun f -> mk_comb_preterm (f,ptm)) @:
         parse_atom_with is_postfix_token)
) src

and parse_preterm2 src = (
  (* Prefix expression *)
  mk_comb_preterm @:
      (parse_atom_with is_prefix_token
       >@> (fun f ->
            let item() = "argument for prefix " ^ quote (atom_preterm_name f) in
            parse_itemB item
               (parse_preterm2 //! hit_infix_err [item])))
  |||
  parse_preterm3
) src

and parse_preterm1 src = (
  (parse_preterm2    //! ((fun ptm -> let x = atom_preterm_name ptm in
                                      "Missing LHS for infix " ^ quote x) @!:
                              parse_atom_with is_infix_token))
  |@| (* Infix expression *)
      parse_infix_expr ("infix", atom_preterm_name)
           (parse_preterm2, parse_infix_op, mk_bin_preterm)
) src

and parse_preterm0 src = (
  (parse_preterm1
                //! early_resword_err [":"] (fun()->"type annotation subterm"))
  |@| (* Type-annotated expression *)
      (fun ptm ->
      (fun pty -> Ptmtyped (ptm,pty)) @:
         (parse_resword ":"
          *>> parse_itemB (fun()->"type annotation type") parse_pretype0))
) src;;

let parse_preterm src = fst (try (
  (parse_start    /! "Empty term quotation")
  *>> (parse_preterm0  //! hit_resword_err (leading_term_reswords ())
                               (fun()->"at start of term"))
  >>* (parse_end   //! hit_resword_err []
                         (fun()->"after syntax-correct leading subterm"))
) src
with ReadFail -> syntax_error "Undiagnosed term syntax error");;



(* ** TOP LEVEL PARSERS ** *)

(* Parsing a type/term quotation breaks down into four main stages:           *)
(*  1. Lexical analysis                                                       *)
(*      - Turns a quotation's character list into a lexical token list;       *)
(*  2. Syntax analysis                                                        *)
(*      - Performed on lexical token list to create a pretype/preterm;        *)
(*  3. Type analysis                                                          *)
(*      - Performed on the pretype/preterm to resolve any unstated types      *)
(*       and/or check type consistency;                                       *)
(*  4. Pretype/preterm conversion                                             *)
(*      - Converts the pretype/preterm into an internal type/term.            *)


(* Type parser *)

(* This takes a string (with the ':', that occurs at the start of a type      *)
(* quotation, removed) and parses it into an internal type.                   *)

let parse_type x =
  (pretype_to_type <* check_pretype <* parse_pretype <* lex <* char_explode) x;;


(* Term parser *)

(* This takes a string and parses it into an internal term.  The type         *)
(* analysis stage first detypes the preterm before inferring types (in        *)
(* 'resolve_preterm'), since the syntax analysis stage gives all variables    *)
(* and constants the null pretype.  Note that type inference is capable of    *)
(* handling overloaded variables.                                             *)

let parse_term x =
  (preterm_to_term <* resolve_preterm <* detype_preterm <* parse_preterm
                                                    <* lex <* char_explode) x;;


(* HOL quotation expansion *)

(* The HOL quotation expansion function is used (in 'holzero.ml') to set the  *)
(* above parsers for types/terms to be the functions that get applied when    *)
(* the ML toplevel encounters type/term quotations respectively.              *)

(* Note that 'parse_type' and 'parse_term' are not module-prefixed in this    *)
(* function (and so type and term quotations require the 'Parser' module to   *)
(* be opened or included in order for parsing to work).  This is because      *)
(* OCaml would otherwise module-prefix the ML type label of any type and term *)
(* quotations entered as top-level ML expressions.                            *)

let string_tail x i = String.sub x i (String.length x - i);;

let rec skip_space x i =
  if (i < String.length x) && (is_whitespace_char (String.get x i))
    then skip_space x (i+1)
    else i;;

let expand_hol_quotation x =
  let i = skip_space x 0 in
  if (i < String.length x) && (String.get x i = ':')
    then let i' = skip_space x (i+1) in
         "parse_type " ^ quote (string_tail x i')
    else "parse_term " ^ quote (string_tail x i);;


end;;
