(* ========================================================================== *)
(* DEFINITION I (HOL Zero)                                                    *)
(* - Derived definition commands for constants                                *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2015                            *)
(* ========================================================================== *)


module Def1 : Def1_sig = struct


(* This module defines a command for defining type bijection constants for a  *)
(* given type constant definition.                                            *)


open DLTree;;

open Equal;;
open EqCong;;
open Bool;;
open BoolClass;;



(* ** TYPE BIJECTIONS DEFINITION ** *)

(* The process of type constant definition results in a theorem stating that  *)
(* a bijection exists between a general instance of the new type constant and *)
(* a prescribed subset of its representation type.  However, it does not      *)
(* actually define such a bijection.  Type bijection definition, defined      *)
(* here, defines two functions, one for mapping from the existing type to the *)
(* new type (the "abstraction function"), and one for mapping from the new    *)
(* type to the existing type (the "representation function").  Both functions *)
(* are bijective between those elements in the prescribed subset of the       *)
(* representation type and all elements of the new type.                      *)


(* Type bijection database *)

let the_type_bijections =
  ref (dltree_empty : (string, (string * string) * (thm * thm)) dltree);;

let get_type_bijection_info x =
  let func = "get_type_bijection_info" in
 try
  dltree_lookup x !the_type_bijections
 with HolFail _ ->
  if (is_tyconst_name x)
    then hol_fail (func, "No bijections defined for type constant " ^ quote x)
    else hol_fail (func, "No type constant called " ^ quote x);;

let get_type_bijections x =
  snd (try2 get_type_bijection_info x    "get_type_bijections");;

let get_all_type_bijections () =
  let xxxtts = dltree_elems !the_type_bijections in
  let xtts = map (fun (x,((x1,x2),(th1,th2))) -> (x,(th1,th2))) xxxtts in
  xtts;;

let get_all_type_bijection_info () = dltree_elems !the_type_bijections;;


(* Type bijection definition command *)

(* new_type_bijections : string -> string * string -> thm * thm               *)
(*                                                                            *)
(* .... *)
(*    |- !a. ABS (REP a) = a      |- !r. P r <=> REP (ABS r) = r              *)

let new_type_bijections x (tyfn1,tyfn2) =
  let func = "new_type_bijections" in
 try
  let th0 = try1 get_tyconst_definition x
                          (* |- ?(f:ty->ty0). TYPE_DEFINITION P f0           *)
                   (func, "Type constant " ^ quote x ^ " not defined") in
  let () = assert0 (cannot get_type_bijections x)       LocalFail in
  let () = assert1 (not (is_const_name tyfn1))
                   (func, "Constant name " ^ quote tyfn1 ^ " already used") in
  let () = assert1 (not (is_const_name tyfn2))
                   (func, "Constant name " ^ quote tyfn2 ^ " already used") in
  let (v0,tm0) = dest_exists (concl th0) in
  let (dp,f0) = dest_comb tm0 in
  let p = rand dp in
  let (ty2,ty1) = dest_fun_type (type_of f0) in
  let absfn = mk_var (tyfn1, mk_fun_type (ty1,ty2)) in
  let repfn = mk_var (tyfn2, mk_fun_type (ty2,ty1)) in
  let f = mk_select (v0,tm0) in
  let th01 = list_app_beta_rhs_rule
           (inst_type_rule [(a_ty,ty1);(b_ty,ty2)] type_definition_def) [p;f] in
                          (* |- TYPE_DEFINITION P f <=>                      *)
                          (*        ONE_ONE f /\ (!x. P x <=> (?y. x = f y)) *)
  let th02 = app_beta_rhs_rule
                (inst_type_rule [(a_ty,ty2);(b_ty,ty1)] one_one_def) f in
                          (* |- ONE_ONE f <=>                                *)
                          (*              (!x1 x2. f x1 = f x2 ==> x1 = x2)  *)
  let th03 = select_rule th0 in                  (* |- TYPE_DEFINITION P f   *)
  let th04 = eq_mp_rule th01 th03 in
                          (* |- ONE_ONE f /\ (!x. P x <=> (?y. x = f y))     *)
  let th0x = eq_mp_rule th02 (conjunct1_rule th04) in
                          (* |- !x1 x2. f x1 = f x2 ==> x1 = x2              *)
  let th0y = conjunct2_rule th04 in
                          (* |- !x. P x <=> (?y. x = f y)                    *)
  let vs = free_vars p in
  let a = variant vs (mk_var ("a",ty2)) in
  let a' = variant (a::vs) (mk_var ("a'",ty2)) in
  let r = variant vs (mk_var ("r",ty1)) in
  let tm1 = mk_comb (f,a) in       (* f a       *)
  let tm2 = mk_comb (p,r) in       (* P r       *)
  let tm3 = mk_eq (a,a') in        (* a = a'    *)
  let thx = list_spec_rule [a;a'] th0x in        (* |- f a = f a' ==> a = a' *)
  let thy = spec_rule r th0y in                  (* |- P r <=> (?y. r = f y) *)
  let th1 = disch_rule tm3 (mk_comb2_rule f (assume_rule tm3)) in
                                                 (* |- a = a' ==> f a = f a' *)
  let th2 = imp_antisym_rule thx th1 in          (* |- f a = f a' <=> a = a' *)
  let th3 = mk_select_rule a' th2 in
                          (* |- (@a'. f a = f a') = (@a'. a = a')            *)
  let tm4 = mk_eq (r,tm1) in       (* r = f a    *)
  let tm5 = mk_abs (r, mk_select (a,tm4)) in   (* \r. @a. r = f a  *)
  let th4 = beta_conv (mk_comb (tm5,tm1)) in
                          (* |- (\r. @a. r = f a) (f a) = (@a'. f a = f a')  *)
  let th5 = exists_rule (mk_exists (a',tm3), a) (eq_refl_conv a) in
                                                 (* |- ?a'. a = a'           *)
  let th6 = select_rule th5 in                   (* |- a = (@a'. a = a')     *)
  let th7 = gen_rule a (list_eq_trans_rule [th4; th3; eq_sym_rule th6]) in
                          (* |- !a. (\r. @a. r = f a) (f a) = a              *)
  let th8 = eq_mp_rule thy (assume_rule tm2) in  (* P r |- ?y. r = f y       *)
  let th9 = select_rule th8 in                   (* P r |- r = f (@y. r = f y)*)
  let tm6 = mk_comb (tm5,r) in     (* (\r. @a. r = f a) r  *)
  let th10 = beta_conv tm6 in
                          (* |- (\r. @a. r = f a) r = (@a. r = f a)          *)
  let th11 = mk_comb2_rule f th10 in
                          (* |- f ((\r. @a. r = f a) r) = f (@a. r = f a)    *)
  let th12 = eq_trans_rule th11 (eq_sym_rule th9) in
                          (* P r |- f ((\r. @a. r = f a) r) = r              *)
  let th13 = disch_rule tm2 th12 in
                          (* |- P r ==> f ((\r. @a. r = f a) r) = r          *)
  let tm7 = mk_exists (a,tm4) in    (* ?a. r = f a   *)
  let tm8 = mk_eq (mk_comb (f,tm6), r) in
  let th14 = exists_rule (tm7,tm6) (eq_sym_rule (assume_rule tm8)) in
                          (* f ((\r. @a. r = f a) r) = r |- ?a. r = f a      *)
  let th15 = eq_mp_rule (eq_sym_rule thy) th14 in
                          (* f ((\r. @a. r = f a) r) = r |- P r              *)
  let th16 = disch_rule tm8 th15 in
                          (* |- f ((\r. @a. r = f a) r) = r ==> P r          *)
  let th17 = gen_rule r (imp_antisym_rule th13 th16) in
                          (* |- !r. P r <=> f ((\r. @a. r = f a) r) = r      *)
  let th18 = conj_rule th7 th17 in
                          (* |- (!a. (\r. @a. r = f a) (f a) = a) /\         *)
                          (*    (!r. P r <=> f ((\r. @a. r = f a) r) = r)    *)
  let tm9 = mk_exists (absfn, subst [(tm5,absfn)] (concl th18)) in
  let tm10 = mk_exists (repfn, subst [(f,repfn)] tm9) in
  let th19 = exists_rule (tm10,f) (exists_rule (tm9,tm5) th18) in
                          (* |- ?rep abs. (!a. abs (rep a) = a) /\           *)
                          (*              (!r. P r <=> rep (abs r) = r)      *)
  let th = new_const_specification ([tyfn2;tyfn1],th19) in
  let (tha,thb) = (conjunct1_rule th, conjunct2_rule th) in
  (the_type_bijections :=
          dltree_insert (x,((tyfn1,tyfn2),(tha,thb))) !the_type_bijections;
   (tha,thb))
 with LocalFail ->
  (* Benign redefinition *)
  let ((x1,x2),_) = get_type_bijection_info x in
  let () = assert1 ((x1 = tyfn1) && (x2 = tyfn2))
             (func, "Type bijection fns already defined for type constant " ^
                    quote x) in
  let (tha,thb) = get_type_bijections x in
  (warn ("Benign redefinition of type bijection fns " ^
                                               quote x1 ^ " and " ^ quote x2);
   (tha,thb));;


end;;
