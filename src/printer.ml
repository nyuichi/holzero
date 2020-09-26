(* ========================================================================== *)
(* PRINTER (HOL Zero)                                                         *)
(* - Pretty printers for types, terms and theorems                            *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2016                            *)
(* ========================================================================== *)


module Printer : Printer_sig = struct


(* This module implements the type, term and theorem pretty printers, for     *)
(* outputting quotation representations of internal types/terms/theorems.     *)
(* The printers take into account name fixity status and enumeration bracket  *)
(* settings (see 'Names' module), certain special-case theory entities (whose *)
(* declarations in later modules are anticipated here), and the display modes *)
(* (see 'DModes' module).  This module is a trusted component of the system,  *)
(* since the user will normally rely on it to determine what has been proved  *)
(* and what has been asserted.                                                *)

(* The printers have the important completeness property that their output is *)
(* unambiguous, so for example there is no confusion about the type of any    *)
(* subterm or about whether a given term atom is a variable or a constant.    *)

(* ! Currently there is no special formatting for multi-line output.          *)


open Format;;

open Type;;
open Term;;
open Thm;;
open Utils1;;

open Names;;
open DModes;;
open Preterm;;
open TypeAnal;;
open TypeAnnot;;



(* ** UTILITIES ** *)


(* Basic printer utils *)

let print_sep x () = print_string x;;

let print_open_brkt () = print_string "(";;

let print_close_brkt () = print_string ")";;

let print_space () = print_string " ";;


(* Conditional printer utils *)

let print_open_brkt_if b = if b then print_open_brkt ();;

let print_close_brkt_if b = if b then print_close_brkt ();;

let print_space_if b = if b then print_space ();;


(* List printer utils *)

let rec print_seplist print_fn print_sep_fn xs =
   match xs with
     []  -> ()
   | [x1]
         -> print_fn x1
   | x1::xs2
         -> (print_fn x1;
             print_sep_fn ();
             print_seplist print_fn print_sep_fn xs2);;

let print_sp_seplist sp print_fn print_sep_fn xs =
  let print_sep_fn1 () = (print_sep_fn (); print_space_if sp) in
  print_seplist print_fn print_sep_fn1 xs;;

let print_splist print_fn xs =
  print_seplist print_fn print_space xs;;


(* Precedence comparison *)

(* This is for determining whether precedence brackets are needed for a       *)
(* subexpression.  Returns "true" if brackets are needed when going from a    *)
(* construct at parse-level 'l0', precedence 'n0' and extra flag 'fl0' to a   *)
(* construct at parse-level 'l1', precedence 'n1'.  If going to a higher      *)
(* parse-level or the same parse-level but higher precedence then no brackets *)
(* are needed.  Flag 'fl0' being set means that brackets are needed if the    *)
(* parse level and precedence are the same.                                   *)

let need_prec_brkts fl0 (l0,n0) (l1,n1) =
  (l1 < l0) ||
  (l1 = l0) && (n1 < n0) ||
  (l1 = l0) && (n1 = n0) && fl0;;


(* Name class comparison *)

(* This is for determining whether separation (be it brackets or spacing) is  *)
(* required between juxtaposed tokens, given the boundary classes of their    *)
(* names.  The following classification is used:                              *)
(*   alphanumerics     1                                                      *)
(*   symbolics         2                                                      *)
(*   quoted/other      0                                                      *)
(* Separation is never required with something of class 0 or with something   *)
(* of a different class.  The 'ss0' arg is a list of boundary classes that    *)
(* could juxtapose - in some cases it's easier to consider the list of        *)
(* possibilities rather than work out which one it is, and over-use of        *)
(* separation is always safe.                                                 *)

let need_separation ss0 s1 = (s1 > 0) && (mem s1 ss0);;



(* ** PRETYPE PRINTER ** *)


(* Token boundary class *)

let type_name_form x =
  if (is_keyword x) || (is_enum_bracket x)
    then 0
  else if (is_alphanum x) || (is_numeric x)
    then 1
  else if (is_symbolic x)
    then 2
    else 0;;


(* Identifier disambiguation markers *)

let type_printable_name x =
  if (is_keyword x) || (is_enum_bracket x)
    then quote x
  else if (is_alphanum x) || (is_numeric x) || (is_symbolic x)
    then x
    else quote x;;

let tyvar_printable_name x =
  let x' = type_printable_name x in
  let x'' = if (get_tyvar_marking_mode () = Full) || (is_tyconst_name x)
              then "'" ^ x'
              else x' in
  x'';;


(* Pretype printer *)

(* The following parse levels are used for type syntax (with higher number    *)
(* indicating tighter binding):                                               *)
(*    Infix type               10                                             *)
(*    Nonfix compound type     20                                             *)

let rec print_pretype0 (ss0,fl0,pr0) pty =
  match pty with
    Ptyvar x
       -> (* Type variable *)
          let x' = tyvar_printable_name x in
          let s1 = type_name_form x in
          (print_open_brkt_if (need_separation ss0 s1);
           print_string x';
           print_close_brkt_if (need_separation ss0 s1))
  | Ptygvar n
       -> (* Generated type variable *)
          (print_open_brkt_if (need_separation ss0 1);
           print_string "%"; print_string (string_of_int n);
           print_close_brkt_if (need_separation ss0 1))
  | Ptycomp (x,ptys)
       -> if (has_infix_type_fixity x)
            then (* Infix compound type *)
                 let (x,ptys) = strip_infix_pretype pty in
                 let (n,h) = get_infix_type_info x in
                 let x' = type_printable_name x in
                 let print_op = print_sep x' in
                 let ss1 = insert (type_name_form x) ss0 in
                 let pr1 = (10,n) in
                 (print_open_brkt_if (need_prec_brkts fl0 pr0 pr1);
                  (match h with
                    LeftAssoc
                       -> (* Left-associative infix type *)
                          (print_pretype0 (ss1,false,pr1) (hd ptys);
                           print_op ();
                           print_seplist
                               (print_pretype0 (ss1,true,pr1)) print_op
                               (tl ptys))
                  | RightAssoc
                       -> (* Right-associative infix type *)
                          (print_seplist
                               (print_pretype0 (ss1,true,pr1)) print_op
                               (front ptys);
                           print_op ();
                           print_pretype0 (ss1,false,pr1) (last ptys))
                  | NonAssoc
                       -> (* Non-associative infix type *)
                          print_seplist      (* Note that length 'ptys' = 2  *)
                               (print_pretype0 (ss1,true,pr1)) print_op
                               ptys);
                  print_close_brkt_if (need_prec_brkts fl0 pr0 pr1))
            else (* Nonfix compound type *)
                 let x' = type_printable_name x in
                 let s1 = type_name_form x in
                 let pr1 = (20,0) in
                 (print_open_brkt_if (need_separation ss0 s1);
                  print_open_brkt_if (is_nonempty ptys);
                  print_seplist (print_pretype0 ([],false,pr1)) (print_sep ",")
                                ptys;
                  print_close_brkt_if (is_nonempty ptys);
                  print_string x';
                  print_close_brkt_if (need_separation ss0 s1));;

let print_pretype ty = print_pretype0 ([],false,(10,0)) ty;;



(* ** PRETERM PRINTERS ** *)

(* Two printers are implemented for preterms: the full printer for full HOL   *)
(* term syntax, and the primitive printer for primitive term syntax.  The     *)
(* printer used depends on the selected language level display mode (see      *)
(* 'DModes' module).                                                          *)


(* Token boundary class *)

let term_name_form x =
  if (is_keyword x) || (is_enum_bracket x)
    then 0
  else if (is_alphanum x)
    then 1
  else if (is_symbolic x)
    then 2
    else 0;;


(* Identifier disambiguation markers *)

let term_printable_name x =
  if (is_keyword x) || (is_enum_bracket x)
    then quote x
  else if (is_alphanum x) || (is_symbolic x)
    then x
    else quote x;;

let var_printable_name x =
  let x' = term_printable_name x in
  if (get_var_marking_mode () = Full) || (is_const_name x)
    then "%" ^ x'
    else x';;

let is_compound_preterm ptm =
  match ptm with
    Ptmvar _ | Ptmconst _
        -> false
  | _   -> true;;


(* Atom printer *)

let rec print_atom ptm =
  match ptm with
    Ptmvar (x,_)
       -> (* Variable *)
          print_string (var_printable_name x)
  | Ptmconst (x,_)
       -> (* Constant *)
          print_string (term_printable_name x)
  | Ptmtyped (ptm0,pty)
       -> (* Type-annotated atom *)
          (print_string "(";
                print_atom ptm0; print_string ":"; print_pretype pty;
           print_string ")")
  | _  -> internal_error "print_atom";;


(* Full preterm printer *)

(* This prints full HOL term syntax, catering for fixities, enumerations and  *)
(* the special-case constants ("COND", "LET", "PAIR" and the numeral          *)
(* constants "BIT0", "BIT1" and "ZERO").  Note that the declarations of these *)
(* special-case constants have not happened at this stage of the build, and   *)
(* so are anticipated by the printer.                                         *)

(* The following parse levels are used for full term syntax (with higher      *)
(* number indicating tighter binding):                                        *)
(*    Type annotation / Enumeration / Pair     5                              *)
(*    Lambda / Binder / Conditional           10                              *)
(*    Infix                                   20                              *)
(*    Prefix                                  30                              *)
(*    Postfix                                 40                              *)
(*    Nonfix                                  50                              *)

let rec print_full_preterm0 (fl0,pr0) ptm =
  if (is_nat_preterm ptm)
    then (* Numeral *)
         let n = dest_nat_preterm_big_int ptm in
         print_string (string_of_big_int n)
  else if (is_enum_preterm ptm)
    then (* Enumeration *)
         let (br1,ptms,br2) = dest_enum_preterm ptm in
         let pr1 = (5,0) in
         let sp = (exists is_compound_preterm ptms) in
         (print_string br1; print_space ();
          print_sp_seplist sp (print_full_preterm0 (false,pr1)) (print_sep ",")
                           ptms;
          print_space (); print_string br2)
  else match ptm with
    Ptmvar (x,_) | Ptmconst (x,_)
       -> if (has_nonfix_fixity x)
            then (* Nonfix atom *)
                 print_atom ptm
            else (* Defixed prefix/infix/postfix/binder atom *)
                 (print_string "$"; print_atom ptm)
  | Ptmcomb _
       -> if (is_cond_preterm ptm)
            then (* Conditional expression *)
                 let (ptm0,ptm1,ptm2) = dest_cond_preterm ptm in
                 let pr1 = (10,0) in
                 (print_open_brkt_if (need_prec_brkts fl0 pr0 pr1);
                  print_string "if "; print_full_preterm0 (true,pr1) ptm0;
                     print_string " then "; print_full_preterm0 (true,pr1) ptm1;
                     print_string " else "; print_full_preterm0 (true,pr1) ptm2;
                  print_close_brkt_if (need_prec_brkts fl0 pr0 pr1))
          else if (is_let_preterm ptm)
            then (* Let-expression *)
                 let (vtms,tm0) = dest_let_preterm ptm in
                 let pr1 = (10,0) in
                 let print_vtm (v,tm) =
                        (print_full_preterm0 (true,pr1) v; print_string " = ";
                            print_full_preterm0 (true,pr1) tm) in
                 (print_open_brkt_if (need_prec_brkts fl0 pr0 pr1);
                  print_string "let ";
                     print_seplist print_vtm (print_sep " and ") vtms;
                     print_string " in "; print_full_preterm0 (true,pr1) tm0;
                  print_close_brkt_if (need_prec_brkts fl0 pr0 pr1))
          else if (is_pair_preterm ptm)
            then (* Pair expression *)
                 let ptms = strip_pair_preterm ptm in
                 let pr1 = (5,0) in
                 let sp = (exists is_compound_preterm ptms) in
                 (print_open_brkt ();
                  print_sp_seplist sp
                         (print_full_preterm0 (false,pr1)) (print_sep ",")
                         ptms;
                  print_close_brkt ())
          else if (is_prefix_preterm ptm)
            then (* Prefix expression *)
                 let (f,ptm0) = dest_comb_preterm ptm in
                 let pr1 = (30,0) in
                 (print_open_brkt_if (need_prec_brkts fl0 pr0 pr1);
                  print_atom f; print_space ();
                     print_full_preterm0 (false,pr1) ptm0;
                  print_close_brkt_if (need_prec_brkts fl0 pr0 pr1))
          else if (is_infix_preterm ptm)
            then (* Infix expression *)
                 let (f,ptms) = strip_infix_preterm ptm in
                 let (n,h) = (get_infix_info <* atom_preterm_name) f in
                 let print_op () =
                    print_space (); print_atom f; print_space () in
                 let pr1 = (20,n) in
                 (print_open_brkt_if (need_prec_brkts fl0 pr0 pr1);
                  (match h with
                    LeftAssoc
                       -> (* Left-associative infix application *)
                          (print_full_preterm0 (false,pr1) (hd ptms);
                           print_op ();
                           print_seplist
                               (print_full_preterm0 (true,pr1)) print_op
                               (tl ptms))
                  | RightAssoc
                       -> (* Right-associative infix application *)
                          (print_seplist
                               (print_full_preterm0 (true,pr1)) print_op
                               (front ptms);
                           print_op ();
                           print_full_preterm0 (false,pr1) (last ptms))
                  | NonAssoc
                       -> (* Non-associative infix application *)
                          print_seplist      (* Note that length 'ptms' = 2  *)
                               (print_full_preterm0 (true,pr1)) print_op
                               ptms);
                  print_close_brkt_if (need_prec_brkts fl0 pr0 pr1))
          else if (is_postfix_preterm ptm)
            then (* Postfix expression *)
                 let (f,ptm0) = dest_comb_preterm ptm in
                 let pr1 = (40,0) in
                 (print_open_brkt_if (need_prec_brkts fl0 pr0 pr1);
                  print_full_preterm0 (true,pr1) ptm0; print_space ();
                     print_atom f;
                  print_close_brkt_if (need_prec_brkts fl0 pr0 pr1))
          else if (is_binder_preterm ptm)
            then (* Binder expression *)
                 let (f,vs,ptm0) = strip_binder_preterm ptm in
                 let pr1 = (10,0) in
                 let sf = term_name_form (atom_preterm_name f) in
                 let s1 = term_name_form (atom_preterm_name (hd vs)) in
                 let s2 = term_name_form (atom_preterm_name (last vs)) in
                 (print_open_brkt_if (need_prec_brkts fl0 pr0 pr1);
                  print_atom f; print_space_if (need_separation [sf] s1);
                     print_splist (print_full_preterm0 (false,pr1)) vs;
                     print_space_if (need_separation [2] s2); print_string ". ";
                     print_full_preterm0 (false,pr1) ptm0;
                  print_close_brkt_if (need_prec_brkts fl0 pr0 pr1))
            else (* Curried function application *)
                 let (f,ptm0) = dest_comb_preterm ptm in
                 let pr1 = (50,0) in
                 (print_open_brkt_if (need_prec_brkts fl0 pr0 pr1);
                  print_full_preterm0 (false,pr1) f; print_space ();
                  print_full_preterm0 (true,pr1) ptm0;
                  print_close_brkt_if (need_prec_brkts fl0 pr0 pr1))
  | Ptmabs _
       -> (* Lambda abstraction *)
          let (vs,ptm0) = strip_abs_preterm ptm in
          let pr1 = (10,0) in
          let s1 = term_name_form (atom_preterm_name (hd vs)) in
          let s2 = term_name_form (atom_preterm_name (last vs)) in
          (print_open_brkt_if (need_prec_brkts fl0 pr0 pr1);
           print_string "\\"; print_space_if (need_separation [2] s1);
              print_splist (print_full_preterm0 (false,pr1)) vs;
              print_space_if (need_separation [2] s2); print_string ". ";
              print_full_preterm0 (false,pr1) ptm0;
           print_close_brkt_if (need_prec_brkts fl0 pr0 pr1))
  | Ptmtyped (ptm0,pty)
       -> (* Type-annotated expression *)
          let pr1 = (5,0) in
          (print_open_brkt_if (need_prec_brkts fl0 pr0 pr1);
           print_full_preterm0 (true,pr1) ptm0;
              print_string ":"; print_pretype pty;
           print_close_brkt_if (need_prec_brkts fl0 pr0 pr1));;

let print_full_preterm ptm = print_full_preterm0 (false,(5,0)) ptm;;


(* Primitive preterm printer *)

(* This prints primitive HOL term syntax.  Identifiers are printed defixed    *)
(* (using "$") if they refer to names with fixity, and enumerations and       *)
(* special case constants are printed without syntactic sugar.  Note that any *)
(* type annotations occurring in the term are printed in full HOL type        *)
(* syntax.                                                                    *)

(* The following parse levels are used for primitive term syntax (with higher *)
(* number indicating tighter binding):                                        *)
(*    Type annotation          5                                              *)
(*    Lambda abstraction      10                                              *)
(*    Nonfix                  50                                              *)

let rec print_prim_preterm0 (fl0,pr0) ptm =
  match ptm with
    Ptmvar (x,_) | Ptmconst (x,_)
       -> if (has_nonfix_fixity x)
            then (* Nonfix atom *)
                 print_atom ptm
            else (* Defixed prefix/infix/postfix/binder atom *)
                 (print_string "$"; print_atom ptm)
  | Ptmcomb _
       -> (* Curried function application *)
          let (f,ptms0) = strip_comb_preterm ptm in
          let pr1 = (50,0) in
          (print_open_brkt_if (need_prec_brkts fl0 pr0 pr1);
           print_splist (print_prim_preterm0 (true,pr1)) (f::ptms0);
           print_close_brkt_if (need_prec_brkts fl0 pr0 pr1) )
  | Ptmabs _
       -> (* Lambda abstraction *)
          let (vs,ptm0) = strip_abs_preterm ptm in
          let pr1 = (10,0) in
          let s1 = term_name_form (atom_preterm_name (hd vs)) in
          let s2 = term_name_form (atom_preterm_name (last vs)) in
          (print_open_brkt_if (need_prec_brkts fl0 pr0 pr1);
           print_string "\\"; print_space_if (need_separation [2] s1);
              print_splist (print_prim_preterm0 (false,pr1)) vs;
              print_space_if (need_separation [2] s2); print_string ".";
              print_space (); print_prim_preterm0 (false,pr1) ptm0;
           print_close_brkt_if (need_prec_brkts fl0 pr0 pr1))
  | Ptmtyped (ptm0,pty)
       -> (* Type-annotated expression *)
          let pr1 = (5,0) in
          (print_open_brkt_if (need_prec_brkts fl0 pr0 pr1);
           print_prim_preterm0 (true,pr1) ptm0;
              print_string ":"; print_pretype pty;
           print_close_brkt_if (need_prec_brkts fl0 pr0 pr1));;

let print_prim_preterm ptm = print_prim_preterm0 (false,(5,0)) ptm;;



(* ** TOP LEVEL PRINTERS ** *)


(* Type printers *)

let print_type ty = (print_pretype <* type_to_pretype) ty; flush stdout;;

let print_qtype ty =
  print_string "`:"; print_type ty; print_string "`"; flush stdout;;


(* Printing preterm *)

(* This gives a preterm for the supplied term, annotated with any types that  *)
(* are needed for printing.  If 'fl' is set, then the type of the overall     *)
(* term is taken as given when deciding type annotations.  Note that the      *)
(* use of 'check_preterm_annotations' on the result removes the need to trust *)
(* the relatively complicated type annotation routine.                        *)

let annotate_preterm pty_ ptm =
  match (get_type_annotation_mode (), get_language_level_mode ()) with
    (Minimal, _)       -> min_annotate_preterm pty_ ptm
  | (Full   , Minimal) -> full_annotate_preterm false ptm
  | (Full   , Full)    -> full_annotate_preterm true ptm;;

let printing_preterm fl tm =
  let pty_ = if fl then Some (type_to_pretype (type_of tm))
                   else None in
  (check_preterm_annotations tm <* annotate_preterm pty_ <*
                                                        term_to_preterm) tm;;


(* Term printers *)

let print_preterm ptm =
  match (get_language_level_mode ()) with
    Minimal -> print_prim_preterm ptm
  | Full    -> print_full_preterm ptm;;

let print_term tm =
  (print_preterm <* printing_preterm false) tm; flush stdout;;

let print_qterm tm =
  print_string "`"; print_term tm; print_string "`"; flush stdout;;


(* Theorem printer *)

(* A hack is used to stop the theorem printer annotating the same vars in     *)
(* different assumptions/conclusion of the theorem.  This involves rolling    *)
(* all the assumptions/conclusion into a single term for type annotation,     *)
(* before getting the appropriately type-annotated preterm, and then          *)
(* unrolling this to get back the constituent parts.  Implication is used to  *)
(* separate the parts, since it has the right type and gets declared in the   *)
(* core theory.  Note that the number of assumptions needs to be considered   *)
(* before unrolling the preterm, in case the conclusion itself has a top-     *)
(* level implication.                                                         *)

let rec ndest_binargs_preterm n ptm =
  if (n > 1)
    then let (_,ptm1,ptm2) = dest_bin_preterm ptm in
         ptm1::(ndest_binargs_preterm (n-1) ptm2)
    else [ptm];;

let thm_printing_preterms th =
  let (hs,c) = dest_thm th in
  let tm = foldr1 (curry mk_imp) (c::hs) in
  let ptm = printing_preterm true tm in
  let (pc,phs) = hd_tl (ndest_binargs_preterm (length hs + 1) ptm) in
  (phs,pc);;

let print_thm th =
  let (hs,c) = thm_printing_preterms th in
  (print_sp_seplist true print_preterm (print_sep ",") hs;
   (if (is_nonempty hs) then print_space ());
   print_string "|-"; print_space ();
   print_preterm c;
   flush stdout);;


end;;
