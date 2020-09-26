(* ========================================================================== *)
(* TYPE ANALYSIS (HOL Zero)                                                   *)
(* - Type analysis of pretypes and preterms                                   *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2013                            *)
(* ========================================================================== *)


module TypeAnal : TypeAnal_sig = struct


(* This module defines type analysis routines for pretypes and preterms, used *)
(* in parsing and printing type/term quotations.  The primary routines are    *)
(* detyping, type unification, type inference and type consistency check.     *)
(* This module is a trusted component of the system, due to its use in the    *)
(* implementation of the pretty printer.                                      *)

(* These facilities support the parser/printer soundness/completeness         *)
(* objectives.  These are: the ability to parse-in a quotation representation *)
(* of any well-formed type/term; the ability to unambiguously print a         *)
(* quotation for any type/term/theorem; and the ability to parse-in the       *)
(* printed quotation representation of any type/term to result in the same    *)
(* internal type/term.  Meeting these objectives means that overloaded        *)
(* variables need special consideration.  The solution is centred around the  *)
(* concept of name closure (see Type Inference section below).                *)


open Type;;
open Term;;
open Utils1;;

open Preterm;;



(* ** UTILITIES ** *)


(* Failure messages *)

(* Type errors are classified into 6 categories, and each category's error    *)
(* message is given here.  They are first raised as HolFail exceptions, and   *)
(* get promoted to HolError exceptions in 'infer_pretypes' and                *)
(* 'check_pretype', by which stage a user error is certain.                   *)

let type_error msg = hol_error ("TYPE ERROR", msg);;

let type_fail_info msg = ("TYPE FAIL", msg);;

let arity_error (x,n1,n2) =
  type_fail_info
    ("Type constant " ^ quote x ^ " has arity " ^ string_of_big_int n1 ^
     " but is used with type param list length " ^ string_of_big_int n2);;

let fun_error1 =
  type_fail_info "Function subterm does not have function type";;

let fun_error2 =
  type_fail_info
     "Function subterm domain type incompatible with argument subterm type";;

let overload_error x =
  type_fail_info
    ("Overloaded var " ^ quote x ^ " type not resolved at name closure");;

let annot_error =
  type_fail_info "Subterm type incompatible with type annotation";;

let types_error =
  type_fail_info "Supplied types do no unify";;


(* Pretype check *)

(* This checks that the supplied pretype is well-formed, by checking that all *)
(* compound types have the correct arity for the type constant involved.      *)
(* This gets used on stand-alone type quotations and on types embedded as     *)
(* type annotations in term quotations.                                       *)

let rec pretype_ok pty =
  match pty with
    Ptyvar _ | Ptygvar _
       -> true
  | Ptycomp (x,ptys)
       -> let n = try1 prim_get_tyconst_arity x     ("pretype_ok","?")  in
          let () = assert1 (eq_big_int (length_big_int ptys) n)
                                   (arity_error (x, n, length_big_int ptys)) in
          (forall pretype_ok ptys);;

let check_pretype pty =
 try
  let _ = pretype_ok pty in
  pty
 with HolFail ("TYPE FAIL",msg) -> type_error msg;;



(* ** PRETERM DETYPING ** *)

(* Preterm detyping is for stripping out from a preterm any existing type     *)
(* information in its atoms, just leaving unchanged the types explicitly      *)
(* given in type annotations.  It gives each occurrence of a var a unique     *)
(* generated tyvar, and each occurrence of a const its generic type with      *)
(* unique generated tyvars for its type parameters.  This is used as a        *)
(* precursor to type inference, ensuring that there are no unintended type    *)
(* dependencies between subterms.                                             *)

let pretype_gvar_counter = ref 0;;

let reset_pretype_gvar_counter () = (pretype_gvar_counter := 0);;

let new_pretype_gvar () =
  let n = !pretype_gvar_counter in
  let () = if not (n < max_int)
             then hol_error ("PARSER/PRINTER LIMITATION",
                             "Exceeded generated type variable maximum") in
  (pretype_gvar_counter := n + 1;
   Ptygvar n);;

let generate_var_preterm x =
  Ptmvar (x, new_pretype_gvar ());;

let generate_const_preterm x =
  let ty = try1 get_const_gtype x        ("generate_const_preterm","?") in
  let tyvs = type_tyvars ty in
  let pty = type_to_pretype ty in
  let foo tyv =
     let x = dest_var_type tyv in
     let pty' = new_pretype_gvar () in
     (Ptyvar x, pty') in
  let theta = map foo tyvs in
  let pty' = pretype_inst theta pty in
  Ptmconst (x,pty');;

let rec detype_preterm0 ptm =
  match ptm with
    Ptmvar (x,_)
       -> generate_var_preterm x
  | Ptmconst (x,_)
       -> generate_const_preterm x
  | Ptmcomb (ptm1,ptm2)
       -> let ptm1' = detype_preterm0 ptm1 in
          let ptm2' = detype_preterm0 ptm2 in
          Ptmcomb (ptm1',ptm2')
  | Ptmabs (v,ptm0)
       -> let v' = detype_preterm0 v in
          let ptm0' = detype_preterm0 ptm0 in
          Ptmabs (v',ptm0')
  | Ptmtyped (ptm0,pty)
       -> let ptm0' = detype_preterm0 ptm0 in
          Ptmtyped (ptm0',pty);;

let detype_preterm ptm =
  let () = reset_pretype_gvar_counter () in
  detype_preterm0 ptm;;



(* ** TYPE UNIFICATION ** *)

(* This algorithm type-unifies two pretypes - i.e. finds an instantiation     *)
(* list for the pretypes' generated tyvars for making the pretypes equal, or  *)
(* otherwise fails if such an instantiation list does not exist.  Instances   *)
(* of the same generated tyvar in both pretypes are assumed to refer to the   *)
(* same generated tyvar.  Note that instns are not found for conventional     *)
(* tyvars (as oppposed to generated tyvars), since these are considered to be *)
(* fixed in inputted term/type quotations.                                    *)


(* Basic pretype unification *)

(* This takes two pretypes and returns an old-to-new instn list for generated *)
(* tyvars, calculated by comparing corresponding subcomponents of the         *)
(* pretypes.  This instn list is not necessarily closed (i.e. it may need to  *)
(* be applied repeatedly until it makes no change) and may contain            *)
(* inconsistencies when when the two pretypes cannot be unified (instead of   *)
(* failing).  These are dealt with by instantiation closure (see below).      *)

let rec basic_unify_pretypes (pty1,pty2) =
  match (pty1,pty2) with
    (pty1, pty2) when (pty1 = pty2)
       -> []
  | (Ptygvar n1, Ptygvar n2)
       -> if (n1 < n2) then [(pty2,pty1)] else [(pty1,pty2)]
  | (Ptygvar _, _)
       -> [(pty1,pty2)]
  | (_, Ptygvar _)
       -> [(pty2,pty1)]
  | (Ptycomp (x1,ptys1), Ptycomp (x2,ptys2))
       -> let () = assert1 (x1 = x2)            types_error in
          flatten (map basic_unify_pretypes (zip ptys1 ptys2))
  | _  -> hol_fail types_error;;


(* Instantiation closure *)

(* This function takes an existing closed pretype instn list 'theta0' and a   *)
(* second (not necessarily closed or consistent) pretype instn list 'theta',  *)
(* and incorporates 'theta' into 'theta0', resulting in either a new closed   *)
(* instn list or failure (if inconsistencies exist in 'theta' wrt 'theta0').  *)

let theta_inst theta0 theta = snd_map (pretype_inst theta0) theta;;

let rec theta_closure theta0 theta =   (* assumes 'theta0' is already closed *)
  match theta with
    (gty,pty)::theta1
       -> let gtys = pretype_gtyvars pty in
          let gtys0 = map fst theta0 in
          if (pty = gty)
            then (* Identity map: remove *)
                 theta_closure theta0 theta1
          else if (mem gty gtys)
            then (* Cyclical map: fail *)
                 hol_fail types_error
          else if (mem gty gtys0)
            then (* Already in 'theta0': unify with existing pretype *)
                 let pty0 = assoc gty theta0 in
                 let theta2 = basic_unify_pretypes (pty,pty0) in
                 theta_closure theta0 (theta2 @ theta1)
          else if not (disjoint gtys gtys0)
            then (* Result includes 'theta0' entry: use 'theta0' on result *)
                 let pty' = pretype_inst theta0 pty in
                 theta_closure theta0 ((gty,pty')::theta1)
            else (* Otherwise: incorporate into 'theta0' *)
                 let theta0' = theta_inst [(gty,pty)] theta0 in
                 theta_closure ((gty,pty)::theta0') theta1
  | [] -> (* No more maps to incorporate: return 'theta0' *)
          theta0;;


(* Full pretype unification *)

(* This unifies any generated tyvars in input pretypes 'pty1' and 'pty2', to  *)
(* result in either a closed pretype instn list for making them equal, or     *)
(* failure (when the pretypes cannot be unified).  In 'unify_pretypes0', the  *)
(* unification is carried out wrt input pretype instn list 'theta0', and the  *)
(* result incorporates 'theta0' (but with its range instantiated according to *)
(* the unification).  Note that 'theta0' is assumed to be closed.             *)

let unify_pretypes0 theta0 (pty1,pty2) =
  let theta12 = basic_unify_pretypes (pty1,pty2) in
  let theta' = theta_closure theta0 theta12 in
  theta';;

let unify_pretypes (pty1,pty2) = unify_pretypes0 [] (pty1,pty2);;


(* Pretype list unification *)

(* This unifies all pretypes in the supplied list with each other,            *)
(* incorporating the result into existing closed instn list 'theta0'.         *)

let unify_pretype_list theta0 ptys =
  let (pty1,ptys2) = hd_tl ptys in
  foldl unify_pretypes0 theta0 (map (pair pty1) ptys2);;


(* Pretypes pairs unification *)

(* This unifies the left pretype with the right pretype of each pair in the   *)
(* supplied list, incorporating all the results into existing closed instn    *)
(* list 'theta0'.                                                             *)

let unify_pretype_pairs theta0 ptyptys =
  foldl unify_pretypes0 theta0 ptyptys;;



(* ** TYPE INFERENCE ** *)

(* Type inference finds the most general pretypes that can be assigned to the *)
(* generated tyvars in a given preterm, to make the preterm ready to be       *)
(* turned into a well-formed term.  Note that the algorithm implemented here  *)
(* goes beyond classic Hindley-Milner type inference to cater for variable    *)
(* overloading.                                                               *)

(* Four basic criteria are used to infer types:                               *)
(*  1. The generic types of constants;                                        *)
(*  2. Types inferred from function applications;                             *)
(*  3. Explicit type annotations embedded within the preterm;                 *)
(*  4. Types inferred from separate occurrences of the same variable at name  *)
(*    closure (see below).                                                    *)

(* The preterm input is assumed to have been detyped, so each occurrence of a *)
(* variable and each occurrence of a polymorphic constant has its own unique  *)
(* generated tyvars, as happens in preterm parsing.  The type inference       *)
(* algorithm then works bottom-up, unifying pretypes as needed and building   *)
(* up an overall instn list for generated tyvars.  Conventional tyvars (as    *)
(* opposed to generated tyvars), that come from user type annotations if the  *)
(* input comes from preterm parsing, are fixed and not subject to             *)
(* unification.  The resulting instn list may still include generated tyvars  *)
(* in its range - these are turned into numbered conventional tyvars          *)
(* elsewhere (during preterm conversion).                                     *)

(* Preterms with overloaded vars (i.e. vars with the same name but different  *)
(* types in the same scope) are supported.  This is necessary for parsing     *)
(* completeness, since variable overloading is allowed in the HOL language.   *)
(* The approach taken centres around the concept of a point of "name closure" *)
(* for a given var name: any subterm at which a var with the given name       *)
(* becomes bound, and the top level of the term if there are any free vars    *)
(* with the given name.  At every point of name closure for a given name,     *)
(* either all free occurrences of vars with the name must refer to the same   *)
(* variable (and thus must all unify), or otherwise they must all have        *)
(* locally fully-resolved types.                                              *)

(* Note that, according to this approach, it is possible to create a          *)
(* quotation representation of any term, no matter how much variable          *)
(* overloading it has, by type-annotating its overloaded vars sufficiently.   *)


(* Variable environment *)

(* A variable environment captures the locally-resolved pretypes of the free  *)
(* vars in a given subterm.  Each entry pairs a var name with a pretype list, *)
(* giving the set of all partially and fully-resolved pretypes for that var   *)
(* name.  The entries are ordered according to var name, to enable faster     *)
(* union and subtraction.  As types are resolved, vars' pretypes get type-    *)
(* instantiated to result in potentially shorter pretype lists.               *)

type varenv = (string * pretype list) list;;

let varenv_inst theta (venv:varenv) : varenv =
  let foo ptys = setify (map (pretype_inst theta) ptys) in
  snd_map foo venv;;

let rec varenv_subtract (venv:varenv) (x,pty) : varenv =
  match venv with
    (x0,ptys)::venv0
       -> if (x = x0)
            then let ptys' = subtract ptys [pty] in
                 if (is_empty ptys')
                   then venv0
                   else (x0,ptys')::venv0
            else (x0,ptys)::(varenv_subtract venv0 (x,pty))
  | [] -> [];;

let rec varenv_union (venv1:varenv) (venv2:varenv) : varenv =
  match (venv1,venv2) with
    ((x1,ptys1)::venv01, (x2,ptys2)::venv02)
            -> if (x1 < x2)
                 then (x1,ptys1)::(varenv_union venv01 venv2)
               else if (x2 < x1)
                 then (x2,ptys2)::(varenv_union venv1 venv02)
                 else (x1, union ptys1 ptys2)::(varenv_union venv01 venv02)
  | (_, []) -> venv1
  | ([], _) -> venv2;;


(* Name closure *)

(* These functions calculate the locally-deduced closed instn list and        *)
(* variable environment resulting at a given var name's point of closure.     *)

let close_name0 venv x theta =
  let ptys = assoc x venv in
  let (ptys1,ptys2) = partition (is_empty <* pretype_gtyvars) ptys in
  match (ptys1,ptys2) with
    (_,[])
        -> (* All 'x's already resolved *)
           theta                                    (* let them be *)
  | ([_],_) | ([],_::_)
        -> (* Some 'x's unresolved, and 0/1 different resolved 'x's *)
           try1 (unify_pretype_list theta) ptys     (* try to unify all 'x's *)
                (overload_error x)                  (* fail if can't unify *)
  | _   -> (* Some 'x's unresolved, and 2 or more different resolved 'x's *)
           hol_fail (overload_error x);;            (* fail *)

let close_name (x,pty) (theta,venv) =
  let theta' = close_name0 venv x theta in
  let pty' = pretype_inst theta' pty in
  let venv' = varenv_subtract (varenv_inst theta' venv) (x,pty') in
  (theta',venv');;

let close_all_names (theta,venv) =
  let xs = setify (map fst venv) in
  let theta' = foldr (close_name0 venv) xs theta in
  theta';;


(* Type inference algorithm *)

(* This performs a single bottom-up pass of a preterm, calculating at each    *)
(* level a provisional most general pretype and a closed instn list, and      *)
(* passing these up to the next level.  The resulting top-level instn list    *)
(* can be used to instantiate the generated tyvars in the preterm to make it  *)
(* well-formed.  Note that the implementation assumes that the preterm input  *)
(* has already been detyped.                                                  *)

(* The var environment is maintained to help infer types for overloaded vars. *)
(* A given var name can have many pretypes, but at a point of name closure    *)
(* (see above), any unresolved pretypes (i.e. that involve generated tyvars)  *)
(* for the given var name must be unified with each other and with any        *)
(* resolved entries for the name.                                             *)

(* Note - To get closed intermediate instn lists when joining the instn lists *)
(* of subterm branches, it is sufficient to simply concatenate the lists      *)
(* (rather than call the relatively-slow instn closure routine).  This is     *)
(* because, due to detyping that will already have taken place, the generated *)
(* tyvars in any subterm are unique to that subterm.                          *)

let rec infer_pretypes0 ptm =
  match ptm with
    Ptmvar (x,pty)
       -> (pty,[],[(x,[pty])])
  | Ptmconst (x,pty)
       -> (pty,[],[])
  | Ptmcomb (ptm1,ptm2)
       -> let (pty1,theta1,venv1) = infer_pretypes0 ptm1 in
          let (pty2,theta2,venv2) = infer_pretypes0 ptm2 in
          let theta12 = theta1 @ theta2 in        (* See Note above *)
          let venv12 = varenv_union venv1 venv2 in
          let (ptya,ptyb) = try  dest_fun_pretype pty1
                            with HolFail _ ->
                            if (is_gtyvar_pretype pty1)
                              then (pty2, new_pretype_gvar ())
                              else hol_fail fun_error1 in
          let ptyab = mk_fun_pretype (ptya,ptyb) in
          let theta = try1
                        (unify_pretype_pairs theta12) [(ptyab,pty1);(ptya,pty2)]
                        fun_error2 in
          let venv = varenv_inst theta venv12 in
          let pty' = pretype_inst theta ptyb in
          (pty',theta,venv)
  | Ptmabs (ptm1,ptm2)
       -> let (pty1,theta1,venv1) = infer_pretypes0 ptm1 in
          let (pty2,theta2,venv2) = infer_pretypes0 ptm2 in
          let x = atom_preterm_name ptm1 in
          let pty12 = mk_fun_pretype (pty1,pty2) in
          let theta12 = theta1 @ theta2 in        (* See Note above *)
          let venv12 = varenv_union venv1 venv2 in
          let (theta,venv) = close_name (x,pty1) (theta12,venv12) in
          let pty' = pretype_inst theta pty12 in
          (pty',theta,venv)
  | Ptmtyped (ptm0,pty)
       -> let _ = pretype_ok pty in      (* fails if 'pty' is ill-formed *)
          let (pty0,theta0,venv0) = infer_pretypes0 ptm0 in
          let theta = try1 (unify_pretypes0 theta0) (pty0,pty)  annot_error in
          let venv = varenv_inst theta venv0 in
          let pty' = pretype_inst theta pty0 in
          (pty',theta,venv);;

let infer_pretypes ptm =
 try
  let (_,theta0,venv) = infer_pretypes0 ptm in
  let theta = close_all_names (theta0,venv) in   (* close top-level var names *)
  theta
 with HolFail ("TYPE FAIL",msg) -> type_error msg;;


(* Resolving preterm types *)

(* This function replaces the generated tyvars in the supplied preterm with   *)
(* their most general valid pretypes, deduced from type inference.  Note that *)
(* the preterm input is assumed to have been detyped.                         *)

let resolve_preterm ptm =
  let theta = infer_pretypes ptm in
  let ptm' = preterm_inst theta ptm in
  ptm';;



(* ** CONSISTENCY CHECKS ** *)


(* Type annotation check *)

(* This is used during printing, after a preterm has been created (from the   *)
(* to-be-printed internal term) and type-annotated, to check that the type    *)
(* annotations are sufficient to deduce all the types in the original term.   *)
(* This removes the need to trust the type annotation source code (in the     *)
(* 'TypeAnnot' module) for the purposes of printer soundness.                 *)

(* The check is done by resolving the types in a detyped version of the       *)
(* supplied preterm, then converting it to a term and checking that this is   *)
(* equal to the supplied internal term.  The type-resolved preterm is         *)
(* returned.                                                                  *)

let check_preterm_annotations tm ptm =
 try
  let ptm0 = detype_preterm ptm in   (* discard all types except annotations *)
  let ptm0' = resolve_preterm ptm0 in
  let tm0' = preterm_to_term ptm0' in
  let () = assert (term_eq tm0' tm) in
  ptm0'
 with HolError _ | HolFail _ | Assert_failure _ ->
  internal_error "check_preterm_annotations";;


end;;
