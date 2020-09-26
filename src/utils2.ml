(* ========================================================================== *)
(* BASIC UTILITIES II (HOL Zero)                                              *)
(* - More basic derived operations on types, terms and theorems               *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2015                            *)
(* ========================================================================== *)


module Utils2 : Utils2_sig = struct


(* This module defines various basic useful operations on types, terms and    *)
(* theorems.                                                                  *)


open Type;;
open Term;;
open Thm;;
open Utils1;;
open Names;;



(* ** TYPE SYNTAX FUNCTIONS ** *)


(* Function types *)

let list_mk_fun_type (tys,ty) = foldr' mk_fun_type (tys,ty);;

let strip_fun_type ty = unfoldr dest_fun_type ty;;



(* ** TERM SYNTAX FUNCTIONS ** *)


(* Function application *)

let rator tm = fst (dest_comb tm);;

let rand tm = snd (dest_comb tm);;

let strip_comb tm = unfoldl dest_comb tm;;


(* Lambda abstraction *)

let list_mk_abs (vs,tm0) = try2 (foldr' mk_abs) (vs,tm0)    "list_mk_abs";;

let bvar tm = fst (dest_abs tm);;

let body tm = snd (dest_abs tm);;

let strip_abs tm = unfoldr dest_abs tm;;


(* Binary/binder expressions *)

let is_cbin x tm = (can (dest_cbin x) tm);;

let is_cbinder x tm = (can (dest_cbinder x) tm);;


(* Equality *)

let eq_lhs tm = fst (dest_eq tm);;

let eq_rhs tm = snd (dest_eq tm);;


(* Implication *)

let list_mk_imp (tms,tm) = try2 (foldr' mk_imp) (tms,tm)    "list_mk_imp";;

let strip_imp tm = unfoldr dest_imp tm;;


(* Selection *)

let mk_select (v,tm0) =
  let () = assert1 (is_bool_term tm0)     ("mk_select","Arg 2 not boolean") in
  let f = mk_iconst ("@", [(a_ty, type_of v)]) in
  try2 mk_binder (f,v,tm0)               "mk_select";;

let dest_select tm =
  try1 (dest_cbinder "@") tm          ("dest_select","Not a selection");;

let is_select tm = (can dest_select tm);;


(* Universal quantifier *)

let mk_forall (v,tm0) =
  let () = assert1 (is_bool_term tm0)      ("mk_forall","Arg 2 not boolean") in
  let f = mk_iconst ("!", [(a_ty, type_of v)]) in
  try2 mk_binder (f,v,tm0)                "mk_forall";;

let list_mk_forall (vs,tm0) =
  try2 (foldr' mk_forall) (vs,tm0)    "list_mk_forall";;

let dest_forall tm =
  try1 (dest_cbinder "!") tm        ("dest_forall","Not a universal");;

let is_forall tm = (can dest_forall tm);;

let strip_forall tm = unfoldr dest_forall tm;;


(* Conjunction *)

let mk_conj (tm1,tm2) =
  let func = "mk_conj" in
  let () = assert1 (is_bool_term tm1)       (func,"Arg 1 not boolean") in
  let () = assert1 (is_bool_term tm2)       (func,"Arg 2 not boolean") in
  let f = mk_gconst "/\\" in
  mk_bin (f,tm1,tm2);;

let list_mk_conj tms = try2 (foldr1' mk_conj) tms     "list_mk_conj";;

let dest_conj tm =
  try1 (dest_cbin "/\\") tm     ("dest_conj","Not a conjunction");;

let is_conj tm = (can dest_conj tm);;

let strip_conj tm = unfoldr1 dest_conj tm;;

let flatstrip_conj tm = unfold dest_conj tm;;



(* ** TERM UTILITIES ** *)


(* Term union *)

let term_union tms1 tms2 = union' alpha_eq tms1 tms2;;


(* Same types *)

let same_types tm1 tm2 = type_eq (type_of tm1) (type_of tm2);;


(* Free variables *)

let list_free_vars tms =
  foldl (fun vs tm -> union' term_eq vs (free_vars tm)) [] tms;;

let rec term_free_in tm00 tm =
  (alpha_eq tm00 tm) ||
  (match (dest_term tm) with
     Term_comb (tm1,tm2)
        -> (term_free_in tm00 tm1) || (term_free_in tm00 tm2)
   | Term_abs (v,tm0)
        -> not (var_free_in v tm00) && (term_free_in tm00 tm0)
   | _  -> false);;


(* Generating variables *)

let genvar_count = ref 0;;

let genvar ty =
  let x = "_" ^ (string_of_int !genvar_count) in
  (genvar_count := !genvar_count + 1;
   mk_var (x,ty));;

let rec list_variant vs0 vs =
  match vs with
    v1::vs1 -> let v1' = variant vs0 v1 in
               let vs1' = list_variant (v1'::vs0) vs1 in
               v1'::vs1'
  | []      -> [];;

let rec list_cvariant vs0 vs =
  match vs with
    v1::vs1 -> let v1' = cvariant vs0 v1 in
               let vs1' = list_cvariant (v1'::vs0) vs1 in
               v1'::vs1'
  | []      -> [];;


(* All variables *)

(* This lists all the variables that occur within the supplied term, either   *)
(* free or bounded.  Note that a variable is listed just once if it occurs    *)
(* both bound and free.                                                       *)

let rec all_vars tm =
  match (dest_term tm) with
    Term_var _
        -> [tm]
  | Term_const _
        -> []
  | Term_comb (tm1,tm2)
        -> union' term_eq (all_vars tm1) (all_vars tm2)
  | Term_abs (v,tm0)
        -> insert' term_eq v (all_vars tm0);;

let list_all_vars tms =
  foldl (fun vs tm -> union' term_eq vs (all_vars tm)) [] tms;;


(* Term substitution *)

(* subst : (term * term) list -> term -> term                                 *)
(*                                                                            *)
(* Performs a single parallel substitution of subterms in the supplied term   *)
(* according to the supplied old-to-new substitution list, replacing all free *)
(* occurrences of substitution list domain elements with their corresponding  *)
(* range elements.  A failure is raised if any list entry domain element has  *)
(* a different type from its range element.                                   *)
(*                                                                            *)
(* Binding variables in the resulting theorem are renamed as necessary to     *)
(* avoid variable capture.  Note that if one domain element occurs free in    *)
(* another, then the list entry with the larger domain element gets used in   *)
(* preference.  And if two domain elements are alpha-equivalent, then the     *)
(* earlier list entry gets used in preference.  List entries that do not      *)
(* apply are ignored, and if no entries apply then the returned term is the   *)
(* same as the input.                                                         *)

(* Special care is taken not to reconstruct subterms that have not changed as *)
(* a result of the substitution, to save on unnecessary garbage collection.   *)

exception Clash of term;;

let rec subst0 vs0 theta tm =
 try
  let (_,tm') = find ((alpha_eq tm) <* fst) theta in
  let vsf' = free_vars tm' in
  if (disjoint' term_eq vsf' vs0)
    then tm'
    else let v_ = find (fun v0 -> mem' term_eq v0 vsf') (rev vs0) in
         raise (Clash v_)
 with HolFail _ ->
  match (dest_term tm) with
    Term_var _ | Term_const _
       -> tm
  | Term_comb (tm1,tm2)
       -> let tm1' = subst0 vs0 theta tm1 in
          let tm2' = subst0 vs0 theta tm2 in
          if (tm1' == tm1) && (tm2' == tm2)  then tm  else mk_comb (tm1',tm2')
  | Term_abs (v,tm0)
       -> let theta' = fst_filter (not <* (var_free_in v)) theta in
       (try
          let tm0' = subst0 (v::vs0) theta' tm0 in
          if (tm0' == tm0)  then tm  else mk_abs (v,tm0')
        with Clash v_ ->
          let () = assert0 (term_eq v v_)   (Clash v_) in
          let vsf = free_vars tm0 in
          let vsf' = flatten (map (free_vars <* snd) theta) in
          let u = cvariant (vs0 @ vsf' @ vsf) v in
          let tm0' = subst0 vs0 ((v,u)::theta') tm0 in
          mk_abs (u,tm0'));;

let subst theta tm =
  let () = assert1 (forall (uncurry same_types) theta)
                       ("subst","Non-equal types in substitution list") in
  subst0 [] theta tm;;


(* Variable matching *)

(* This takes a term pattern and a term match, and returns a var instn list   *)
(* for vars in the pattern for making it equal to the match.  An error is     *)
(* raised if the match does not fit the pattern.                              *)

let rec var_match0 btheta theta patt tm =
  let func = "var_match" in
  match (dest_term patt, dest_term tm) with
    (Term_var _, _)
       -> if (can (assoc patt) btheta)
            then (* Bound variable match *)
                 let tm' = assoc patt btheta in
                 let () = assert1 (term_eq tm' tm)     (func,"Match failure") in
                 let patt' = try1 (inv_assoc tm) btheta
                                                       (func,"Match failure") in
                 let () = assert1 (term_eq patt' patt) (func,"Match failure") in
                 theta
            else (* Free variable match *)
                 let () = assert1 (forall (fun v-> cannot (inv_assoc v) btheta)
                                          (free_vars tm))
                                                       (func,"Match failure") in
                 if (can (assoc patt) theta)
                   then (* Existing match *)
                        let tm' = assoc patt theta in
                        let () = assert1 (alpha_eq tm tm')
                                                       (func,"Match failure") in
                        theta
                   else (* New match *)
                        let theta1 = (patt,tm)::theta in
                        theta1
  | (Term_const _, Term_const _)
       -> let () = assert1 (term_eq patt tm)           (func,"Match failure") in
          theta
  | (Term_comb (patt1,patt2), Term_comb (tm1,tm2))
       -> let theta1 = var_match0 btheta theta patt1 tm1 in
          let theta2 = var_match0 btheta theta1 patt2 tm2 in
          theta2
  | (Term_abs (pattv,patt0), Term_abs (v,tm0))
       -> let theta1 = var_match0 ((pattv,v)::btheta) theta patt0 tm0 in
          theta1
  | _  -> hol_fail (func,"Match failure");;

let var_match patt tm = var_match0 [] [] patt tm;;


(* Full term matching *)

(* This takes a term pattern and a term match, and returns a var instn list   *)
(* and a tyvar instn list, respectively for vars and tyvars in the pattern,   *)
(* for making it equal to the match (the tyvar instn is to be applied before  *)
(* the var instn).  An error is raised if the match does not fit the pattern. *)

let rec term_match0 btheta (theta,tytheta) patt tm =
  let func = "term_match" in
  match (dest_term patt, dest_term tm) with
    (Term_var _, _)
       -> let tytheta1 = type_match0 tytheta (type_of patt) (type_of tm) in
          let patt' = tyvar_inst tytheta1 patt in
          if (can (assoc patt') btheta)
            then (* Bound variable match *)
                 let tm' = assoc patt' btheta in
                 let () = assert1 (term_eq tm' tm)    (func,"Match failure") in
                 let patt'' = try1 (inv_assoc tm) btheta
                                                      (func,"Match failure") in
                 let () = assert1 (term_eq patt'' patt')
                                                      (func,"Match failure") in
                 (theta,tytheta1)
            else (* Free variable match *)
                 let () = assert1 (forall (fun v -> cannot (inv_assoc v) btheta)
                                          (free_vars tm))
                                                      (func,"Match failure") in
                 if (can (assoc patt') theta)
                   then (* Existing match *)
                        let tm' = assoc patt' theta in
                        let () = assert1 (alpha_eq tm tm')
                                                      (func,"Match failure") in
                        (theta, tytheta1)
                   else (* New match *)
                        let theta1 = (patt',tm)::theta in
                        (theta1,tytheta1)
  | (Term_const _, Term_const _)
       -> let tytheta1 = type_match0 tytheta (type_of patt) (type_of tm) in
          let patt' = tyvar_inst tytheta1 patt in
          let () = assert1 (patt' = tm)               (func,"Match failure") in
          (theta,tytheta1)
  | (Term_comb (patt1,patt2), Term_comb (tm1,tm2))
       -> let (theta1,tytheta1) =
                       term_match0 btheta (theta,tytheta) patt1 tm1 in
          let (theta2,tytheta2) =
                       term_match0 btheta (theta1,tytheta1) patt2 tm2 in
          (theta2,tytheta2)
  | (Term_abs (pattv,patt0), Term_abs (v,tm0))
       -> let tytheta1 = type_match0 tytheta (type_of pattv) (type_of v) in
          let pattv' = tyvar_inst tytheta1 pattv in
          let (theta2,tytheta2) =
                 term_match0 ((pattv',v)::btheta) (theta,tytheta1) patt0 tm0 in
          (theta2,tytheta2)
  | _   -> hol_fail (func,"Match failure");;

let term_match patt tm = term_match0 [] ([],[]) patt tm;;


(* Renaming binding variables *)

let rename_bvar x' tm =
  let func = "rename_bvar" in
  let (v,tm0) = try1 dest_abs tm       (func,"Not a lambda abstraction") in
  let v' = mk_var (x', type_of v) in
  let () = assert1 (not (var_free_in v' tm))
                                   (func,"New variable occurs free in term") in
  let tm0' = var_inst [(v,v')] tm0 in
  let tm' = mk_abs (v',tm0') in
  tm';;


(* Finding subterms *)

let rec find_subterm test_fn tm =
  if (test_fn tm)
    then tm
    else match (dest_term tm) with
           Term_comb (tm1,tm2)
               -> (try
                     find_subterm test_fn tm1
                   with HolFail _ ->
                     find_subterm test_fn tm2)
         | Term_abs (v,tm0)
               -> find_subterm test_fn tm0
         | _   -> hol_fail ("find_subterm","No subterm fits");;

let rec find_subterms0 tms test_fn tm =
  if (test_fn tm)
    then tm::tms
    else match (dest_term tm) with
           Term_comb (tm1,tm2)
               -> let tms' = find_subterms0 tms test_fn tm2 in
                  let tms'' = find_subterms0 tms' test_fn tm1 in
                  tms''
         | Term_abs (v,tm0)
               -> find_subterms0 tms test_fn tm0
         | _   -> tms;;

let find_subterms test_fn tm = find_subterms0 [] test_fn tm;;



(* ** THEOREM SYNTAX FUNCTIONS ** *)


(* Equality theorems *)

let dest_eqthm th = dest_eq (concl th);;

let eqthm_lhs th = eq_lhs (concl th);;

let eqthm_rhs th = eq_rhs (concl th);;

let is_eqthm th = is_eq (concl th);;



(* ** THEOREM UTILITIES ** *)


(* Theorem free variables *)

let thm_free_vars th =
  let (hs,c) = dest_thm th in
  let hvss = map free_vars hs in
  let cvs = free_vars c in
  union' term_eq (unions' term_eq hvss) cvs;;


(* Theorem equivalence *)

let thm_alpha_eq th1 th2 =
  let (hs1,c1) = dest_thm th1 in
  let (hs2,c2) = dest_thm th2 in
  (alpha_eq c1 c2) &&
  (set_eq' alpha_eq hs1 hs2);;


end;;
