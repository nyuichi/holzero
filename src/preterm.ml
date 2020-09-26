(* ========================================================================== *)
(* PRETYPES AND PRETERMS (HOL Zero)                                           *)
(* - Intermediate datatypes for types/terms used in parsing and printing      *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2016                            *)
(* ========================================================================== *)


module Preterm : Preterm_sig = struct


(* This module defines the pretype and preterm datatypes (called 'pretype'    *)
(* and 'preterm'), and various basic operations on them.  These are used      *)
(* during parsing and printing as intermediate representations of types/terms *)
(* between their quotation and internal representations.  They incorporate    *)
(* extra datatype classes, that don't occur in the corresponding internal     *)
(* datatypes and are only used during parsing and printing.  Being            *)
(* intermediate datatypes, there is no need for well-formedness restrictions  *)
(* on their constructors, and so the datatypes are not made abstract.         *)

(* This module is a trusted component of the system, due to its use in the    *)
(* implementation of the pretty printer.                                      *)


open Type;;
open Term;;
open Utils1;;

open Names;;



(* ** PRETYPE DATATYPE ** *)

(* This is the datatype for the intermediate representation of HOL types.  It *)
(* includes an extra class for "generated tyvars", used in term parsing and   *)
(* printing as a temporary placeholder for an as-yet-undetermined type        *)
(* (whereas "conventional tyvars" come from user annotations and internal     *)
(* types and are fixed for the purposes of parsing and printing).  Generated  *)
(* tyvars have a number attribute.  This is by default '0', which imparts no  *)
(* information, but gets assigned a unique non-zero value during preterm      *)
(* detyping (see 'TypeAnal' module).                                          *)

type pretype =
   Ptyvar of string
 | Ptygvar of int                       (* generated tyvars *)
 | Ptycomp of (string * pretype list);;



(* ** PRETYPE SYNTAX FUNCTIONS ** *)


(* Type variables *)

let dest_tyvar_pretype pty =
  match pty with
    Ptyvar x -> x
  | _        -> hol_fail ("dest_tyvar_pretype","?");;

let dest_gtyvar_pretype pty =
  match pty with
    Ptygvar n -> n
  | _         -> hol_fail ("dest_gtyvar_pretype","?");;

let is_gtyvar_pretype pty = can dest_gtyvar_pretype pty;;


(* Infix types *)

let mk_bin_pretype (x,ptm1,ptm2) = Ptycomp (x,[ptm1;ptm2]);;

let dest_infix_pretype pty =
  let (x,pty1,pty2) = match pty with
                        Ptycomp (x,[ptm1;ptm2]) -> (x,ptm1,ptm2)
                      | _  -> hol_fail ("dest_infix_pretype","?") in
  let () = assert1 (has_infix_type_fixity x)      ("dest_infix_pretype","?") in
  (x,pty1,pty2);;

let rec strip_infix_pretype0 (x,h) pty =
  try
    let (x0,pty1,pty2) = dest_infix_pretype pty in
    let () = assert0 (x0 = x)     LocalFail in
    match h with
      LeftAssoc  -> (strip_infix_pretype0 (x,h) pty1) @ [pty2]
    | RightAssoc -> pty1::(strip_infix_pretype0 (x,h) pty2)
    | NonAssoc   -> [pty1;pty2]
  with HolFail _ | LocalFail -> [pty];;

let strip_infix_pretype pty =
  let (x,_,_) = dest_infix_pretype pty in
  let (n,h) = get_infix_type_info x in
  let ptys = strip_infix_pretype0 (x,h) pty in
  (x,ptys);;


(* Function types *)

let mk_fun_pretype (pty1,pty2) = mk_bin_pretype ("->",pty1,pty2);;

let dest_fun_pretype pty =
  match pty with
    Ptycomp ("->",[pty1;pty2]) -> (pty1,pty2)
  | _                          -> hol_fail ("dest_fun_pretype","?");;


(* Boolean types *)

let bool_pty = Ptycomp ("bool",[]);;

let bool_bin_pty =
  mk_fun_pretype (bool_pty, mk_fun_pretype (bool_pty,bool_pty));;



(* ** PRETYPE UTILITIES ** *)


(* Creating pretypes *)

let rec type_to_pretype ty =
  match (dest_type ty) with
    Type_var x
       -> Ptyvar x
  | Type_comp (x,tys)
       -> let ptys = map type_to_pretype tys in
          Ptycomp (x,ptys);;


(* Pretype conversion *)

(* pretype_to_type0 - Takes mapping for use in preterm conversion.            *)

let rec pretype_to_type0 nxs pty =
  match pty with
    Ptyvar x
       -> mk_var_type x
  | Ptygvar n
       -> let x = assoc n nxs in
          mk_var_type x
  | Ptycomp (x,ptys)
       -> let tys = map (pretype_to_type0 nxs) ptys in
          mk_comp_type (x,tys);;

(* Type quotations do not contain generated tyvars, and so an empty mapping   *)
(* is passed.                                                                 *)

let pretype_to_type pty = pretype_to_type0 [] pty;;


(* Listing pretype variables *)

let rec pretype_tyvars pty =
  match pty with
    Ptyvar _
       -> [pty]
  | Ptygvar _
       -> []
  | Ptycomp (x,ptys)
       -> unions (map pretype_tyvars ptys);;

let rec pretype_gtyvars pty =
  match pty with
    Ptyvar _
       -> []
  | Ptygvar _
       -> [pty]
  | Ptycomp (x,ptys)
       -> unions (map pretype_gtyvars ptys);;

let rec pretype_has_gtyvars pty =
  match pty with
    Ptyvar _
       -> false
  | Ptygvar _
       -> true
  | Ptycomp (_,ptys)
       -> (exists pretype_has_gtyvars ptys);;


(* Instantiating pretypes *)

let rec pretype_inst theta pty =
  match pty with
    Ptyvar _
       -> (try  assoc pty theta  with HolFail _ ->  pty)
  | Ptygvar _
       -> (try  assoc pty theta  with HolFail _ ->  pty)
  | Ptycomp (x,ptys)
       -> let ptys' = map (pretype_inst theta) ptys in
          if (list_eq (==) ptys' ptys)  then pty  else Ptycomp (x,ptys');;


(* Pretype complexity *)

let rec pretype_complexity pty =
  match pty with
    Ptyvar _ | Ptygvar _
       -> 1
  | Ptycomp (_,ptys)
       -> let ns = map pretype_complexity ptys in
          foldl1 (+) (1::ns);;



(* ** PRETERM DATATYPE ** *)

(* This is the datatype for the intermediate representation of HOL terms.  It *)
(* includes an extra class for type-annotated terms, to tie a subterm to a    *)
(* supplied type.  These enable the user and/or the printer to disambiguate   *)
(* terms quotations.                                                          *)

type preterm =
   Ptmvar of (string * pretype)
 | Ptmconst of (string * pretype)
 | Ptmcomb of (preterm * preterm)
 | Ptmabs of (preterm * preterm)
 | Ptmtyped of (preterm * pretype);;          (* type-annotated preterms *)



(* ** PRETERM SYNTAX FUNCTIONS ** *)

(* Note that it's important for the preterm destructors not to remove type    *)
(* annotations, since the destructors are used by the printer, after the      *)
(* preterm type check.                                                        *)

(* Boolean equality is handled specially on conversion between terms and      *)
(* preterms.  This is because the alias "<=>" can be used in term quotations, *)
(* and thus in preterms, but boolean equality is still represented internally *)
(* by the general equality function "=".                                      *)


(* Variables *)

(* Variable preterms are created with a null generated tyvar as their         *)
(* pretype.  This gets replaced during type analysis.                         *)

let mk_nulltype_var_preterm x = Ptmvar (x, Ptygvar 0);;

let rec dest_var_preterm ptm =
  match ptm with
    Ptmvar (x,pty) -> (x,pty)
  | _              -> hol_fail ("dest_var_preterm","?");;


(* Constants *)

(* Constant preterms are created with a null generated tyvar as their         *)
(* pretype.  This gets replaced during type analysis.                         *)

let mk_nulltype_const_preterm x = Ptmconst (x, Ptygvar 0);;

let const_preterm_name ptm =
  match ptm with
    Ptmconst (x,_) -> x
  | _              -> hol_fail ("const_preterm_name","?");;


(* Function application *)

let mk_comb_preterm (f,ptm) = Ptmcomb (f,ptm);;

let list_mk_comb_preterm (f,ptms) = foldl' mk_comb_preterm (f,ptms);;

let dest_comb_preterm ptm =
  match ptm with
    Ptmcomb (ptm1,ptm2) -> (ptm1,ptm2)
  | _                   -> hol_fail ("dest_comb_preterm","?");;

let strip_comb_preterm ptm = unfoldl dest_comb_preterm ptm;;


(* Lamda abstractions *)

let list_mk_abs_preterm (vs,ptm0) =
  foldr (fun v ptm -> Ptmabs (v,ptm)) vs ptm0;;

let dest_abs_preterm ptm =
  match ptm with
    Ptmabs (v,ptm0) -> (v,ptm0)
  | _               -> hol_fail ("dest_abs_preterm","?");;

let strip_abs_preterm ptm = unfoldr dest_abs_preterm ptm;;


(* Type annotations *)

let is_typed_preterm ptm =
  match ptm with
    Ptmtyped _ -> true
  | _          -> false;;


(* Atoms *)

let rec is_atom_preterm ptm =
  match ptm with
    Ptmvar _ | Ptmconst _ -> true
  | Ptmtyped (ptm0,_)     -> is_atom_preterm ptm0
  | _                     -> false;;

let rec atom_preterm_name ptm =
  match ptm with
    Ptmvar (x,_) | Ptmconst (x,_)
                      -> x
  | Ptmtyped (ptm0,_) -> atom_preterm_name ptm0
  | _  -> hol_fail ("atom_preterm_name","?");;

let rec same_atom_preterm ptm1 ptm2 =
  match (ptm1,ptm2) with
    (Ptmvar (x1,pty1), Ptmvar (x2,pty2)) -> (x1 = x2) && (pty1 = pty2)
  | (Ptmconst (x1,_), Ptmconst (x2,_))   -> (x1 = x2)
  | (Ptmtyped (ptm0,_), _)               -> (same_atom_preterm ptm0 ptm2)
  | (_, Ptmtyped (ptm0,_))               -> (same_atom_preterm ptm1 ptm0)
  | (_, _)                               -> hol_fail ("same_atom_preterm","?");;


(* Binary function application *)

let mk_bin_preterm (ptmf,ptm1,ptm2) = list_mk_comb_preterm (ptmf,[ptm1;ptm2]);;

let list_mk_bin_preterm h f ptms =
  match h with
    LeftAssoc  -> foldl1 (fun ptm1 ptm2 -> mk_bin_preterm (f,ptm1,ptm2)) ptms
  | RightAssoc -> foldr1 (fun ptm1 ptm2 -> mk_bin_preterm (f,ptm1,ptm2)) ptms
  | NonAssoc   -> match ptms with
                    [ptm1;ptm2] -> mk_bin_preterm (f,ptm1,ptm2)
                  | _           -> hol_fail ("list_mk_bin_preterm","?");;

let dest_bin_preterm ptm =
  let (ptm01,ptm2) = dest_comb_preterm ptm in
  let (f,ptm1) = dest_comb_preterm ptm01 in
  (f,ptm1,ptm2);;

let dest_bin_preterm0 f0 ptm =
  let (f,ptm1,ptm2) = dest_bin_preterm ptm in
  let () = assert1 (same_atom_preterm f0 f)   ("dest_bin_preterm0","") in
  (ptm1,ptm2);;

let strip_bin_preterm h f0 ptm =
 try
  match h with
    LeftAssoc  -> unfoldl1 (dest_bin_preterm0 f0) ptm
  | RightAssoc -> unfoldr1 (dest_bin_preterm0 f0) ptm
  | NonAssoc   -> let (ptm1,ptm2) = dest_bin_preterm0 f0 ptm in
                  [ptm1;ptm2]
 with HolFail _ -> [ptm];;


(* Conditionals *)

let cond_fn = mk_nulltype_const_preterm "COND";;

let mk_cond_preterm (ptm0,ptm1,ptm2) =
  list_mk_comb_preterm (cond_fn,[ptm0;ptm1;ptm2]);;

let dest_cond_preterm ptm =
  match (strip_comb_preterm ptm) with
    (Ptmconst ("COND",_), [ptm1;ptm2;ptm3]) -> (ptm1,ptm2,ptm3)
  | _ -> hol_fail ("dest_cond_preterm","?");;

let is_cond_preterm ptm = can dest_cond_preterm ptm;;


(* let-expressions *)

(* The 'let_fn' constant has a null generated tyvar.  This will do both for   *)
(* 'mk_let_preterm' (because it then goes on for type analysis), and          *)
(* 'dest_let_preterm' (because it is only used as basis for bin-stripping).   *)

let let_fn = mk_nulltype_const_preterm "LET";;

let mk_let_preterm (vptms,ptm0) =
  let (vs,ptms) = unzip vptms in
  let ptm1 = list_mk_abs_preterm (vs,ptm0) in
  list_mk_bin_preterm LeftAssoc let_fn (ptm1::ptms);;

let dest_let_preterm ptm =
  let (ptm1,ptms) = hd_tl (strip_bin_preterm LeftAssoc let_fn ptm) in
  let () = assert1 (is_nonempty ptms)        ("dest_let_preterm","?") in
  let (vs,ptm2) = strip_abs_preterm ptm1 in
  let (vs1,vs2) = cut_big_int (length_big_int ptms) vs in
  let ptm0 = list_mk_abs_preterm (vs2,ptm2) in
  let vptms = zip vs1 ptms in
  (vptms,ptm0);;

let is_let_preterm ptm = can dest_let_preterm ptm;;


(* Pairs *)

(* The 'pair_fn' constant has a null generated tyvar.  This will do both for  *)
(* 'mk_pair_preterm' (because it then goes on for type analysis), and         *)
(* 'strip_pair_preterm' (because it is only used as basis for bin-stripping). *)

let pair_fn = mk_nulltype_const_preterm "PAIR";;

let mk_pair_preterm (ptm1,ptm2) = mk_bin_preterm (pair_fn,ptm1,ptm2);;

let list_mk_pair_preterm ptms = list_mk_bin_preterm RightAssoc pair_fn ptms;;

let strip_pair_preterm ptm = strip_bin_preterm RightAssoc pair_fn ptm;;

let is_pair_preterm ptm = can (dest_bin_preterm0 pair_fn) ptm;;


(* Natural numerals *)

(* Note that the destructor for numerals ensures that "BIT0" is not applied   *)
(* to "ZERO", thus ensuring that numerals have unique representation.         *)

let numeral_fn = mk_nulltype_const_preterm "NUMERAL";;

let rec mk_nat_preterm_big_int0 n =
  if (gt_big_int n big_int_0)
    then let (n0,n1) = quomod_big_int n big_int_2 in
         let ptmf = if (eq_big_int n1 big_int_0)
                      then mk_nulltype_const_preterm "BIT0"
                      else mk_nulltype_const_preterm "BIT1" in
         let ptm0 = mk_nat_preterm_big_int0 n0 in
         mk_comb_preterm (ptmf,ptm0)
  else if (eq_big_int n big_int_0)
    then mk_nulltype_const_preterm "ZERO"
    else hol_fail ("mk_nat_preterm_big_int","?");;

let mk_nat_preterm_big_int n =
  mk_comb_preterm (numeral_fn, mk_nat_preterm_big_int0 n);;

let rec dest_nat_preterm_big_int0 zok ptm =
 try
  let (ptmf,ptm0) = try0 dest_comb_preterm ptm     LocalFail in
  let x = const_preterm_name ptmf in
  if (x = "BIT0")
    then let n0 = dest_nat_preterm_big_int0 false ptm0 in
         mult_big_int big_int_2 n0
  else if (x = "BIT1")
    then let n0 = dest_nat_preterm_big_int0 true ptm0 in
         add_big_int (mult_big_int big_int_2 n0) big_int_1
    else hol_fail ("dest_nat_preterm_big_int","?")
 with LocalFail ->
  let x = const_preterm_name ptm in
  let () = assert1 ((x = "ZERO") && zok)     ("dest_nat_preterm_big_int","?") in
  big_int_0;;

let dest_nat_preterm_big_int ptm =
  let (f,ptm0) = dest_comb_preterm ptm in
  let () = assert1 (same_atom_preterm f numeral_fn)
                   ("dest_nat_preterm_big_int","?") in
  dest_nat_preterm_big_int0 true ptm0;;

let is_nat_preterm ptm = can dest_nat_preterm_big_int ptm;;


(* Enumerations *)

let mk_enum_preterm (br1,ptms,br2) =
  let zero = get_enum_bracket_zero br1 in
  let f = get_enum_zero_op zero in
  let (br1',br2') = get_enum_zero_brackets zero in
  let () = assert1 ((br1' = br1) && (br2' = br2))     ("mk_enum_preterm","?") in
  let fptm = mk_nulltype_const_preterm f in
  let zptm = mk_nulltype_const_preterm zero in
  list_mk_bin_preterm RightAssoc fptm (ptms@[zptm]);;

let dest_enum_preterm ptm =
 try
  let (fptm,ptm1,ptm2) = try0 dest_bin_preterm ptm     LocalFail in
  let x = const_preterm_name fptm in
  let ptms0 = strip_bin_preterm RightAssoc fptm ptm in
  let (ptms,z) = front_last ptms0 in
  let zero = const_preterm_name z in
  let () = assert1 (get_enum_zero_op zero = x)      ("dest_enum_preterm","?") in
  let (br1,br2) = get_enum_zero_brackets zero in
  (br1,ptms,br2)
 with LocalFail ->
  (* Empty enumeration *)
  let zero = const_preterm_name ptm in
  let (br1,br2) = get_enum_zero_brackets zero in
  (br1,[],br2);;

let is_enum_preterm ptm = can dest_enum_preterm ptm;;


(* Prefix/Infix/Postfix *)

let strip_infix_preterm ptm =
  let (f,ptm1,ptm2) = dest_bin_preterm ptm in
  let x = atom_preterm_name f in
  let (n,h) = get_infix_info x in
  let ptms = strip_bin_preterm h f ptm in
  (f,ptms);;

let is_prefix_preterm ptm =
 try
  let (f,_) = dest_comb_preterm ptm in
  let x = atom_preterm_name f in
  (has_prefix_fixity x)
 with HolFail _ -> false;;

let is_infix_preterm ptm =
 try
  let (f,_,_) = dest_bin_preterm ptm in
  let x = atom_preterm_name f in
  (has_infix_fixity x)
 with HolFail _ -> false;;

let is_postfix_preterm ptm =
 try
  let (f,_) = dest_comb_preterm ptm in
  let x = atom_preterm_name f in
  (has_postfix_fixity x)
 with HolFail _ -> false;;


(* Binders *)

let mk_binder_preterm (f,v,ptm0) =
  Ptmcomb (f, Ptmabs (v,ptm0));;

(* Note that, in compound binders, if the binder in the quotation is type-    *)
(* annotated, then this means the same annotation is used for each subterm.   *)

let list_mk_binder_preterm (f,vs,ptm0) =
  foldr (fun v ptm -> mk_binder_preterm (f,v,ptm)) vs ptm0;;

let dest_binder_preterm ptm =
  let (f,ptm1) = dest_comb_preterm ptm in
  let x = atom_preterm_name f in
  let () = assert1 (has_binder_fixity x)        ("dest_binder_preterm","?") in
  let (v,ptm0) = dest_abs_preterm ptm1 in
  (f,v,ptm0);;

let rec strip_binder_preterm0 f0 ptm =
  try
    let (f,v,ptm0) = dest_binder_preterm ptm in
    let () = assert0 (same_atom_preterm f0 f)     LocalFail in
    let (vs,ptm00) = strip_binder_preterm0 f0 ptm0 in
    (v::vs,ptm00)
  with HolFail _ | LocalFail -> ([],ptm);;

let strip_binder_preterm ptm =
  let (f,v,ptm0) = dest_binder_preterm ptm in
  let (vs,ptm1) = strip_binder_preterm0 f ptm0 in
  (f,v::vs,ptm1);;

let is_binder_preterm ptm = can dest_binder_preterm ptm;;



(* ** PRETERM UTILITIES ** *)


(* Creating preterms *)

(* Creates a trivial preterm version of the supplied term, without any type   *)
(* annotation or generated tyvars.                                            *)

let rec term_to_preterm tm =
  match (dest_term tm) with
    Term_var (x,ty)
       -> let ty' = type_to_pretype ty in
          Ptmvar (x,ty')
  | Term_const (x,ty)
       -> let pty = type_to_pretype ty in
          let x' = if (x = "=") && (pty = bool_bin_pty) then "<=>" else x in
          Ptmconst (x',pty)
  | Term_comb (tm1,tm2)
       -> let ptm1 = term_to_preterm tm1 in
          let ptm2 = term_to_preterm tm2 in
          Ptmcomb (ptm1,ptm2)
  | Term_abs (v,tm0)
       -> let pv = term_to_preterm v in
          let ptm0 = term_to_preterm tm0 in
          Ptmabs (pv,ptm0);;


(* Listing functions *)

let rec preterm_tyvars ptm =
  match ptm with
    Ptmvar (x,pty)
       -> pretype_tyvars pty
  | Ptmconst (x,pty)
       -> pretype_tyvars pty
  | Ptmcomb (ptm1,ptm2)
       -> union (preterm_tyvars ptm1) (preterm_tyvars ptm2)
  | Ptmabs (ptm1,ptm2)
       -> union (preterm_tyvars ptm1) (preterm_tyvars ptm2)
  | Ptmtyped (ptm0,pty)
       -> union (preterm_tyvars ptm0) (pretype_tyvars pty);;

let rec preterm_gtyvars ptm =
  match ptm with
    Ptmvar (x,pty)
       -> pretype_gtyvars pty
  | Ptmconst (x,pty)
       -> pretype_gtyvars pty
  | Ptmcomb (ptm1,ptm2)
       -> union (preterm_gtyvars ptm1) (preterm_gtyvars ptm2)
  | Ptmabs (ptm1,ptm2)
       -> union (preterm_gtyvars ptm1) (preterm_gtyvars ptm2)
  | Ptmtyped (ptm0,pty)
       -> union (preterm_gtyvars ptm0) (pretype_gtyvars pty);;

let rec preterm_has_gtyvars ptm =
  match ptm with
    Ptmvar (_,pty) | Ptmconst (_,pty)
       -> (pretype_has_gtyvars pty)
  | Ptmcomb (ptm1,ptm2) | Ptmabs (ptm1,ptm2)
       -> (preterm_has_gtyvars ptm1) || (preterm_has_gtyvars ptm2)
  | Ptmtyped (ptm0,_)
       -> (preterm_has_gtyvars ptm0);;


(* Preterm conversion *)

(* Preterm conversion turns a preterm into an internal term.  This is used    *)
(* during parsing and the type consistency check in printing.  All pretypes   *)
(* must already be unified, otherwise term construction will fail (because    *)
(* the primitive term constructors check for compatible types).               *)

(* Generated tyvars are mapped to conventional tyvars with number names, from *)
(* 1 upwards and not clashing with existing tyvars in the term.               *)

(* preterm_to_term0 - Basic preterm conversion, given gen tyvar mapping.      *)

let rec preterm_to_term0 nxs ptm =
  match ptm with
    Ptmvar (x,pty)
       -> let ty = pretype_to_type0 nxs pty in
          mk_var (x,ty)
  | Ptmconst (x,pty)
       -> let ty = pretype_to_type0 nxs pty in
          let x' = if (x = "<=>") then "=" else x in
          mk_const (x',ty)
  | Ptmcomb (ptm1,ptm2)
       -> let tm1 = preterm_to_term0 nxs ptm1 in
          let tm2 = preterm_to_term0 nxs ptm2 in
          mk_comb (tm1,tm2)
  | Ptmabs (ptm1,ptm2)
       -> let tm1 = preterm_to_term0 nxs ptm1 in
          let tm2 = preterm_to_term0 nxs ptm2 in
          mk_abs (tm1,tm2)
  | Ptmtyped (ptm0,pty)
       -> preterm_to_term0 nxs ptm0;;    (* type annotation is just ignored *)

(* tynum_mapping - Create gtyvar number to tyvar name mapping, avoiding 'xs0' *)

let rec tynum_mapping0 xs0 i ns =
  match ns with
    n::ns1 -> let x = string_of_int i in
              if (mem x xs0)
                then tynum_mapping0 xs0 (i+1) ns
                else (n,x)::(tynum_mapping0 xs0 (i+1) ns1)
  | []     -> [];;

let tynum_mapping xs0 ns =
  tynum_mapping0 xs0 1 (mergesort (<) ns);;

(* preterm_to_term *)

let preterm_to_term ptm =
  let xs0 = map dest_tyvar_pretype (preterm_tyvars ptm) in
  let ns = map dest_gtyvar_pretype (preterm_gtyvars ptm) in
  let nxs = tynum_mapping xs0 ns in
  preterm_to_term0 nxs ptm;;


(* Instantiating preterms *)

let rec preterm_inst theta ptm =
  match ptm with
    Ptmvar (x,pty)
       -> let pty' = pretype_inst theta pty in
          if (pty' == pty)  then ptm  else Ptmvar (x,pty')
  | Ptmconst (x,pty)
       -> let pty' = pretype_inst theta pty in
          if (pty' == pty)  then ptm  else Ptmconst (x,pty')
  | Ptmcomb (ptm1,ptm2)
       -> let ptm1' = preterm_inst theta ptm1 in
          let ptm2' = preterm_inst theta ptm2 in
          if (ptm1' == ptm1) && (ptm2' == ptm2)
            then ptm
            else Ptmcomb (ptm1',ptm2')
  | Ptmabs (pv,ptm0)
       -> let pv' = preterm_inst theta pv in
          let ptm0' = preterm_inst theta ptm0 in
          if (pv' == pv) && (ptm0' == ptm0)
            then ptm
            else Ptmabs (pv',ptm0')
  | Ptmtyped (ptm0,pty)
       -> let ptm0' = preterm_inst theta ptm0 in
          let pty' = pretype_inst theta pty in
          if (ptm0' == ptm0) && (pty' == pty)
            then ptm
            else Ptmtyped(ptm0',pty');;


(* Matching pretypes *)

let remove_identities theta =
  filter (fun (x,y) -> not (x = y)) theta;;

let rec pretype_match0 theta (mpty,pty) =
  let func = "pretype_match" in
  match (mpty,pty) with
    (Ptygvar _, _)
       -> if (can (assoc mpty) theta)
            then let pty' = assoc mpty theta in
                 let () = assert1 (pty = pty')      (func,"?") in
                 theta
            else (mpty,pty)::theta
  | (Ptyvar mx, Ptyvar x)
       -> let () = assert1 (x = mx)      (func,"?") in
          []
  | (Ptycomp (mx,mptys), Ptycomp (x,ptys))
       -> let () = assert1 (x = mx)      (func,"?") in
          foldr (swap_arg pretype_match0) (zip mptys ptys) theta
  | _  -> hol_fail (func,"?");;

let pretype_match (mpty,pty) =
  remove_identities (pretype_match0 [] (mpty,pty));;

let rec preterm_pretype_match0 theta (mptm,ptm) =
  let func = "pretype_match" in
  match (mptm,ptm) with
    (Ptmvar (mx,mpty), Ptmvar (x,pty)) | (Ptmconst (mx,mpty), Ptmconst (x,pty))
       -> let () = assert1 (x = mx)        (func,"?") in
          pretype_match0 theta (mpty,pty)
  | (Ptmcomb (mptm1,mptm2), Ptmcomb (ptm1,ptm2))
                                   | (Ptmabs (mptm1,mptm2), Ptmabs (ptm1,ptm2))
       -> let theta' = preterm_pretype_match0 theta (mptm1,ptm1) in
          let theta'' = preterm_pretype_match0 theta' (mptm2,ptm2) in
          theta''
  | (Ptmtyped (mptm0,mpty), _)
       -> preterm_pretype_match0 theta (mptm0,ptm)  (* Ignore type annotation *)
  | _  -> hol_fail (func,"?");;

let preterm_pretype_match (mptm,ptm) =
  remove_identities (preterm_pretype_match0 [] (mptm,ptm));;


end;;
