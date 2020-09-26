(* ========================================================================== *)
(* BASIC UTILITIES I (HOL Zero)                                               *)
(* - Essential basic derived operations on types and terms                    *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2013                            *)
(* ========================================================================== *)


module Utils1 : Utils1_sig = struct


(* This module defines various basic operations on types and terms that get   *)
(* used in the implementation of the primitive inference rules and primitive  *)
(* assertion commands in the 'Thm' module.  This module is a trusted          *)
(* component of the system.                                                   *)


open Type;;
open Term;;



(* ** TYPE SYNTAX FUNCTIONS ** *)


(* General type destructor *)

type destructed_type =
    Type_var of string
  | Type_comp of (string * hol_type list);;

let dest_type ty =
  if (is_var_type ty)
    then Type_var (dest_var_type ty)
    else Type_comp (dest_comp_type ty);;


(* Boolean type *)

(* A discriminator for the boolean base type is defined here, in anticipation *)
(* of its introduction in the 'CoreThry' module.                              *)

let is_bool_type ty =
  try
    let (x,_) = dest_comp_type ty in
    (x = "bool")
  with HolFail _ -> false;;


(* Commonly used type variables *)

let a_ty = mk_var_type "a";;
let b_ty = mk_var_type "b";;
let c_ty = mk_var_type "c";;



(* ** TYPE UTILITIES ** *)


(* Listing type variables *)

(* This lists all the type variables that occur in a type.                    *)

let rec type_tyvars ty =
  match (dest_type ty) with
    Type_var _
       -> [ty]
  | Type_comp (_,tys)
       -> unions' type_eq (map type_tyvars tys);;


(* Type matching *)

(* This takes a type pattern and a type match, and returns an old-to-new      *)
(* tyvar instn list for tyvars in the type pattern to make it equal to the    *)
(* match.  A failure is raised if the match doesn't fit the pattern.          *)

let rec type_match0 theta patt ty =
  let func = "type_match" in
  match (dest_type patt, dest_type ty) with
    (Type_var xpatt, _)
        -> (try
              let ty' = try0 (assoc patt) theta     LocalFail in
              let () = assert1 (type_eq ty ty')     (func, "Match failure") in
              theta
            with LocalFail ->
              (patt,ty)::theta)
  | (Type_comp (xpatt,patts), Type_comp (x,tys))
        -> let () = assert1 (x = xpatt)             (func, "Match failure") in
           foldl (uncurry <* type_match0) theta (zip patts tys)
  | _   -> hol_fail (func, "Match failure");;

let type_match patt ty = type_match0 [] patt ty;;



(* ** TERM SYNTAX FUNCTIONS ** *)

(* This section defines some derived syntax functions for the primitive term  *)
(* constructs.  In addition, syntax functions are also provided for equality, *)
(* implication and the existential quantifier, in anticipation of the         *)
(* introduction of their HOL constants in the 'CoreThry' module.              *)


(* General term destructor *)

type destructed_term =
    Term_var of (string * hol_type)
  | Term_const of (string * hol_type)
  | Term_comb of (term * term)
  | Term_abs of (term * term);;

let dest_term tm =
  if (is_var tm)
    then Term_var (dest_var tm)
  else if (is_const tm)
    then Term_const (dest_const tm)
  else if (is_comb tm)
    then Term_comb (dest_comb tm)
    else Term_abs (dest_abs tm);;


(* Constants *)

(* A derived constructor for constants is defined here.  It takes a constant  *)
(* name and a type, where the type must be a valid match for the constant's   *)
(* generic type.  It returns the constant with the supplied type as its type. *)

let mk_const (x,ty) =
  let func = "mk_const" in
  let ty0 = try2 get_const_gtype x         func in
  let theta = try1 (type_match ty0) ty
                        (func, "Type doesn't match generic type of constant") in
  mk_iconst (x,theta);;

let const_name tm = try2 (fst <* dest_const) tm     "const_name";;

let const_type tm = try2 (snd <* dest_const) tm     "const_type";;


(* Variables *)

let var_name tm = try2 (fst <* dest_var) tm     "var_name";;

let var_type tm = try2 (snd <* dest_var) tm     "var_type";;


(* Function application *)

let list_mk_comb (tm,tms) = try2 (foldl' mk_comb) (tm,tms)    "list_mk_comb";;


(* Binary operator expressions *)

let mk_bin (f,tm1,tm2) = try2 list_mk_comb (f,[tm1;tm2])      "mk_bin";;

let dest_bin tm =
 try
  let (ftm1,tm2) = dest_comb tm in
  let (f,tm1) = dest_comb ftm1 in
  (f,tm1,tm2)
 with HolFail _ -> hol_fail ("dest_bin","Not a binary operator expression");;

let is_bin tm = (can dest_bin tm);;

let dest_cbin x tm =
 try
  let (f,tm1,tm2) = dest_bin tm in
  let () = assert0 (const_name f = x)      LocalFail in
  (tm1,tm2)
 with HolFail _ | LocalFail ->
             hol_fail ("dest_cbin","Not the specified binary expression");;


(* Binder expressions *)

let mk_binder (f,v,tm0) =
  try2 mk_comb (f, mk_abs (v,tm0))    "mk_binder";;

let dest_binder tm =
 try
  let (f,tm1) = dest_comb tm in
  let (v,tm0) = dest_abs tm1 in
  (f,v,tm0)
 with HolFail _ -> hol_fail ("dest_binder", "Not a binder expression");;

let dest_cbinder x tm =
 try
  let (f,v,tm0) = try2 dest_binder tm     "dest_cbinder" in
  let () = assert0 (const_name f = x)      LocalFail in
  (v,tm0)
 with HolFail _ | LocalFail ->
            hol_fail ("dest_cbinder", "Not the specified binder expression");;

let is_binder tm = (can dest_binder tm);;


(* Boolean-valued terms *)

let is_bool_term tm = is_bool_type (type_of tm);;


(* Equality *)

let mk_eq (tm1,tm2) =
  let (ty1,ty2) = (type_of tm1, type_of tm2) in
  let () = assert1 (type_eq ty1 ty2)
                   ("mk_eq","Arg 1 type not equal to Arg 2 type") in
  let f = mk_iconst ("=", [(a_ty,ty1)]) in
  mk_bin (f,tm1,tm2);;

let dest_eq tm = try1 (dest_cbin "=") tm     ("dest_eq","Not an equality");;

let is_eq tm = (can dest_eq tm);;


(* Implication *)

let mk_imp (tm1,tm2) =
  let func = "mk_imp" in
  let (ty1,ty2) = (type_of tm1, type_of tm2) in
  let () = assert1 (is_bool_type ty1)       (func,"Arg 1 not boolean") in
  let () = assert1 (is_bool_type ty2)       (func,"Arg 2 not boolean") in
  let f = mk_gconst "==>" in
  mk_bin (f,tm1,tm2);;

let dest_imp tm = try1 (dest_cbin "==>") tm  ("dest_imp","Not an implication");;

let is_imp tm = (can dest_imp tm);;


(* Existential quantification *)

let mk_exists (v,tm0) =
  let func = "mk_exists" in
  let ty = try1 var_type v                   (func,"Arg 1 not a variable") in
  let ty0 = type_of tm0 in
  let () = assert1 (is_bool_type ty0)        (func,"Arg 2 not boolean") in
  let f = mk_iconst ("?", [(a_ty,ty)]) in
  mk_binder (f,v,tm0);;

let list_mk_exists (vs,tm0) =
  try2 (foldr' mk_exists) (vs,tm0)      "list_mk_exists";;

let dest_exists tm =
  try1 (dest_cbinder "?") tm        ("dest_exists","Not an existential");;

let strip_exists tm = unfoldr dest_exists tm;;

let is_exists tm = (can dest_exists tm);;



(* ** TERM UTILITIES ** *)


(* Listing term tyvars *)

(* This lists all the type variables that occur in any subterm of a given     *)
(* term.                                                                      *)

let rec term_tyvars tm =
  match (dest_term tm) with
    Term_var (_,ty) | Term_const (_,ty)
       -> type_tyvars ty
  | Term_comb (tm1,tm2)
       -> union' type_eq (term_tyvars tm1) (term_tyvars tm2)
  | Term_abs (v,tm0)
       -> union' type_eq (term_tyvars v) (term_tyvars tm0);;


(* Alpha equivalence *)

(* Two terms are alpha-equivalent iff they are equal modulo names chosen for  *)
(* bound variables.  This fundamental concept of term equivalence is used     *)
(* throughout the system.                                                     *)

(* Note that the implementation assumes 'assoc' and 'inv_assoc' look up from  *)
(* the front of the list.                                                     *)

let rec alpha_eq0 theta0 tm1 tm2 =
  match (dest_term tm1, dest_term tm2) with
    (Term_var _, Term_var _)
       -> let tm1' = try  assoc tm1 theta0  with HolFail _ ->  tm1  in
          let tm2' = try  inv_assoc tm2 theta0  with HolFail _ ->  tm2  in
          (term_eq tm1' tm2) && (term_eq tm2' tm1)
  | (Term_const _, Term_const _)
       -> (term_eq tm1 tm2)
  | (Term_comb (tm1a,tm1b), Term_comb (tm2a,tm2b))
       -> (alpha_eq0 theta0 tm1a tm2a) && (alpha_eq0 theta0 tm1b tm2b)
  | (Term_abs (v1,tm01), Term_abs (v2,tm02))
       -> let theta0' = (v1,v2)::theta0 in
          let (ty1,ty2) = (var_type v1, var_type v2) in
          (type_eq ty1 ty2) && (alpha_eq0 theta0' tm01 tm02)
  | _  -> false;;

let alpha_eq tm1 tm2 = (term_eq tm1 tm2) || (alpha_eq0 [] tm1 tm2);;


(* Free variables *)

(* The free variables of a term are those variables that occur in the term    *)
(* and are unbounded by any lambda abstraction.                               *)

let rec free_vars tm =
  match (dest_term tm) with
    Term_var _
       -> [tm]
  | Term_const _
       -> []
  | Term_comb (tm1,tm2)
       -> union' term_eq (free_vars tm1) (free_vars tm2)
  | Term_abs (v,tm0)
       -> subtract' term_eq (free_vars tm0) [v];;

let rec var_free_in0 v tm =
  match (dest_term tm) with
    Term_var _
       -> (term_eq v tm)
  | Term_const _
       -> false
  | Term_comb (tm1,tm2)
       -> (var_free_in0 v tm1) || (var_free_in0 v tm2)
  | Term_abs (v0,tm0)
       -> not (term_eq v v0) && (var_free_in0 v tm0);;

let var_free_in v tm =
  let () = assert1 (is_var v)        ("var_free_in","Arg 1 not a variable") in
  var_free_in0 v tm;;


(* Generating variables *)

(* These functions append apostrophes to the end of the supplied variable's   *)
(* name until it avoids the names of any variables in the supplied avoidance  *)
(* list.  No apostrophes are appended if the original name is ok.  The        *)
(* 'cvariant' function also avoids the names of any declared constants.  Any  *)
(* non-variables supplied cause failure.                                      *)

let variant vs0 v =
  let func = "variant" in
  let (x,ty) = try1 dest_var v           (func,"Not a variable") in
  let xs0 = try1 (map var_name) vs0      (func,"Non-var in avoidance list") in
  let x1 = string_variant xs0 x in
  mk_var (x1,ty);;

let rec cvariant_name xs0 x =
  let x1 = string_variant xs0 x in
  if (is_const_name x1)
    then cvariant_name xs0 (x1 ^ "'")
    else x1;;

let cvariant vs0 v =
  let func = "cvariant" in
  let (x,ty) = try1 dest_var v           (func,"Not a variable") in
  let xs0 = try1 (map var_name) vs0      (func,"Non-var in avoidance list") in
  let x' = cvariant_name xs0 x in
  mk_var (x',ty);;


(* Term variable instantiation *)

(* var_inst : (term * term) list -> term -> term                              *)
(*                                                                            *)
(* Performs a single parallel instantiation of the free variables in the      *)
(* supplied term according to the supplied old-to-new variable instantiation  *)
(* list.  All free occurrences of instantiation list domain elements in the   *)
(* term get replaced.  Any domain elements that are not variables cause       *)
(* failure, as do any list entries where the type of the range element        *)
(* differs from the type of the domain element.                               *)
(*                                                                            *)
(* Binding variables in the resulting theorem are renamed as necessary to     *)
(* avoid variable capture.  Note that instantiation list entries that do not  *)
(* apply to the term are ignored, as are repeated entries for a given         *)
(* variable (beyond its first entry).  If no instantiation list entries       *)
(* apply, then the supplied term is returned.                                 *)

(* Variable capture is potentially caused by free vars in the instn range     *)
(* becoming bound by the surrounding term where they are inserted.  This is   *)
(* avoided by giving fresh names to any surrounding binding vars that would   *)
(* otherwise clash.  To identify where variable capture would occur, the      *)
(* 'vs0' list of surrounding binding vars is passed down through subterms.    *)
(* If a clash is spotted during the instn of a var, then a 'Clash' exception  *)
(* is raised and passed back up until caught at the lambda abstraction that   *)
(* creates the outermost offending binding var.  At this point, the binding   *)
(* var is given a fresh, non-clashing name and var instn is reattempted.      *)
(* Eventually all offending binding vars will get renamed and the             *)
(* instantiation will succeed.                                                *)

(* Special care is taken not to reconstruct subterms that have not changed as *)
(* a result of the instantiation, to save on unnecessary garbage collection.  *)

(* Inputs to 'var_inst0':                                                     *)
(*   vs0    - Surrounding binding vars                                        *)
(*   theta  - The specified mapping of free variables to new values           *)
(*   tm     - The term/subterm undergoing possible instantiation              *)

exception Clash of term;;

let rec var_inst0 vs0 theta tm =
  match (dest_term tm) with
    Term_var _
       -> (try
            let tm' = assoc tm theta in      (* HolFail if var not in 'theta' *)
            let vsf' = free_vars tm' in
            if (disjoint' term_eq vsf' vs0)
              then (* Free var instantiation doesn't clash *)
                   tm'
              else (* Free var instantiation contains free vars that clash *)
                   let v_ = find (fun v0 -> mem' term_eq v0 vsf') (rev vs0) in
                   raise (Clash v_)          (* raise Clash for outermost var *)
          with HolFail _ ->
            (* Free/bound var not instantiated *)
            tm)
  | Term_const _
       -> (* Constant *)
          tm
  | Term_comb (tm1,tm2)
       -> let tm1' = var_inst0 vs0 theta tm1 in
          let tm2' = var_inst0 vs0 theta tm2 in
          (* Function application with no clash in subterms *)
          if (tm1' == tm1) && (tm2' == tm2)  then tm  else mk_comb (tm1',tm2')
  | Term_abs (v,tm0)
       -> let theta' = fst_filter (fun v1 -> not (term_eq v1 v)) theta in
       (try
          let tm0' = var_inst0 (v::vs0) theta' tm0 in
          (* Lambda abstraction with no clash in subterm *)
          if (tm0' == tm0)  then tm  else mk_abs (v,tm0')
        with Clash v_ ->
          (* Lambda abstraction with clash in subterm *)
          let () = assert0 (term_eq v v_) (Clash v_) in (* reraise if not 'v' *)
          let foo v = try  free_vars (assoc v theta)  with HolFail _ -> [v] in
          let avs = flatten (map foo (free_vars tm0)) in
          let v' = cvariant avs v in           (* generate fresh name for 'v' *)
          let tm0' = var_inst0 vs0 ((v,v')::theta') tm0 in
          mk_abs (v',tm0'));;

let var_inst theta tm =
  let func = "var_inst" in
 try
  match theta with
    [] -> tm
  | _  -> let () = assert1 (forall (is_var <* fst) theta)
                             (func, "Non-variable in instantiation domain") in
          let () = assert1
                     (forall (fun (v,tm') ->(type_eq (type_of tm') (type_of v)))
                             theta)
                     (func, "Non-equal types in instantiation list") in
          var_inst0 [] theta tm
 with Clash _ -> internal_error func;;


(* Type variable instantiation *)

(* tyvar_inst : (hol_type * hol_type) list -> term -> term                    *)
(*                                                                            *)
(* Performs a single parallel instantiation of the type variables in the      *)
(* supplied term (in its constant and variable atoms) according to the        *)
(* supplied old-to-new instantiation list.  All occurrences of instantiation  *)
(* list domain elements in the term get replaced.  Any domain elements that   *)
(* are not type variables cause failure.                                      *)
(*                                                                            *)
(* Binding variables in the resulting theorem are renamed as necessary to     *)
(* avoid variable capture.  Note that instantiation list entries that do not  *)
(* apply are ignored, as are repeated entries for a given type variable       *)
(* (beyond its first entry).  If no instantiation list entries apply, then    *)
(* the supplied term is returned.                                             *)

(* Note that there is potential for variable capture because HOL allows       *)
(* variable overloading (i.e. vars with the same name but different types in  *)
(* overlapping scopes).  Type instantiating so that two overloaded vars end   *)
(* up with the same type will cause variable capture iff at least one of them *)
(* is a binding var.  Note that this can happen even if one of the vars keeps *)
(* its original type (because the other var, be it the outer- or the inner-   *)
(* scoped var, may get type-instantiated to become equal to it).              *)

(* The solution is to give fresh names to any existing binding vars that,     *)
(* after type instn, would otherwise clash with other vars free in their      *)
(* scope, thus maintaining the separation between different variables.  To    *)
(* identify where variable capture would occur, the association list          *)
(* 'theta0', of original and corresponding type-instantiated binding vars, is *)
(* passed down through subterms.  If a clash is spotted during the type instn *)
(* of a var subterm, then a 'Clash' exception is raised and passed back up    *)
(* until caught at the lambda abstraction that creates the offending binding  *)
(* var, where the binding var is given a fresh, non-clashing name and type    *)
(* instn is reattempted.  Eventually all offending binding vars will get      *)
(* renamed and the type instantiation will succeed.                           *)

(* Special care is taken not to reconstruct subterms that have not changed as *)
(* a result of the instantiation, to save on unnecessary garbage collection.  *)

(* Note - Importantly, 'theta0' is added to from the front.  This ensures     *)
(* that, when there is more than one binding var that gets type-instantiated  *)
(* to the same given var, then the appropriate binding var (i.e. the          *)
(* innermost) is identified for renaming (because 'inv_assoc' works left-to-  *)
(* right).                                                                    *)

(* Inputs to 'tyvar_inst0':                                                   *)
(*   theta0  - Mapping of surrounding binding vars to their new values        *)
(*   tytheta - The specified mapping of type variables to new values          *)
(*   tm      - The term/subterm undergoing possible instantiation             *)

let rec tyvar_inst0 theta0 tytheta tm =
  match (dest_term tm) with
    Term_var (x,ty)
       -> let ty' = type_inst tytheta ty in
          let tm' = if (ty' == ty)  then tm  else mk_var (x,ty')  in
       (try
          let v0 = inv_assoc tm' theta0 in      (* HolFail if 'tm'' not bound *)
          if (term_eq v0 tm)
            then (* Bound var stays bound to same lambda abstraction *)
                 tm'
            else (* Free/bound var becomes inner-bound and so clashes *)
                 raise (Clash v0)
        with HolFail _ ->
          (* Free var stays free *)
          tm')
  | Term_const (x,ty)
       -> (* Constant *)
          let ty' = type_inst tytheta ty in
          if (type_eq ty' ty)  then tm  else mk_const (x,ty')
  | Term_comb (tm1,tm2)
       -> let tm1' = tyvar_inst0 theta0 tytheta tm1 in
          let tm2' = tyvar_inst0 theta0 tytheta tm2 in
          (* Function application with no clash in subterms *)
          if (tm1' == tm1) && (tm2' == tm2)  then tm  else mk_comb (tm1',tm2')
  | Term_abs (v,tm0)
       -> let v' = tyvar_inst0 [] tytheta v in
       (try
          let tm0' = tyvar_inst0 ((v,v')::theta0) tytheta tm0 in  (* See Note *)
          (* Lambda abstraction with no clash in subterm *)
          if (v' == v) && (tm0' == tm0)  then tm  else mk_abs (v',tm0')
        with Clash v_ ->
          (* Lambda abstraction with clash in subterm *)
          let () = assert0 (term_eq v v_)
                           (Clash v_) in        (* reraise if not for 'v' *)
          let v' = cvariant (free_vars tm0) v in(* generate fresh name for 'v'*)
          let tm0' = var_inst0 [] [(v,v')] tm0 in
          let v'' = tyvar_inst0 [] tytheta v' in
          let tm0'' = tyvar_inst0 theta0 tytheta tm0' in
          mk_abs (v'',tm0''));;

let tyvar_inst tytheta tm =
  let func = "tyvar_inst" in
 try
  match tytheta with
    [] -> tm
  | _  -> let () = assert1 (forall (is_var_type <* fst) tytheta)
                          (func,"Non-type-variable in instantiation domain") in
          tyvar_inst0 [] tytheta tm
 with Clash _ -> internal_error func;;


end;;
