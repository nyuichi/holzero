(* ========================================================================== *)
(* DEFINITION II (HOL Zero)                                                   *)
(* - Derived definition commands for non-recursive and recursive functions    *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2015                            *)
(* ========================================================================== *)


module Def2 : Def2_sig = struct


(* This module defines two specialised forms of definition for function       *)
(* constants.  The first form is for non-recursive functions and the second   *)
(* is for recursive functions.                                                *)


open DLTree;;

open Def1;;

open Equal;;
open Bool;;
open BoolClass;;
open Pair;;



(* ** UTILITIES ** *)


(* extract *)

let extract n xs =
  let (xs1,xs02) = cut (n-1) xs in
  let (x,xs2) = hd_tl xs02 in
  (x,xs1@xs2);;


(* inject *)

let inject n x xs =
  let (xs1,xs2) = cut (n-1) xs in
  (xs1 @ [x] @ xs2);;


(* bag_subtract *)

let rec remove xs y =
  match xs with
    x0::xs1 -> if (x0 = y) then xs1
                           else x0::(remove xs1 y)
  | []      -> [];;

let bag_subtract xs ys = foldl remove xs ys;;


(* flat_conjuncts_rule *)

let rec flat_conjuncts_rule0 ths th =
  if (is_conj (concl th))
    then let ths' = flat_conjuncts_rule0 ths (conjunct2_rule th) in
         let ths'' = flat_conjuncts_rule0 ths' (conjunct1_rule th) in
         ths''
    else th::ths;;

let flat_conjuncts_rule th = flat_conjuncts_rule0 [] th;;



(* ** NON-RECURSIVE FUNCTION DEFINITION ** *)

(* Function definition caters for a simple non-recursive style of defining    *)
(* function constants.  It involves supplying an equality term, where the LHS *)
(* is the new function (or actually a placeholder for it) applied to a series *)
(* of variable structure arguments, and the RHS is the result of this         *)
(* application in terms of the variable arguments.  Note that the RHS is not  *)
(* allowed to include the new function.  The RHS is then turned into a        *)
(* lambda abstraction binding the variables in the LHS arguments, and this    *)
(* becomes the definition term that is passed for primitive constant          *)
(* definition.  Note that if there are no LHS arguments, then this is the     *)
(* same as the constant definition style defined in the 'Def1' module.        *)


(* Function definition database *)

let the_fun_defs = ref (dltree_empty : (string,thm) dltree);;

let get_fun_definition x =
 try
  dltree_lookup x !the_fun_defs
 with HolFail _ ->
  let func = "get_fun_definition" in
  let () = assert1 (is_const_name x) (func, "No constant called " ^ quote x) in
  hol_fail (func, "No function definition for constant " ^ quote x);;

let get_all_fun_definitions () = dltree_elems !the_fun_defs;;


(* fst_snd_conv : term -> thm                                                 *)
(*                                                                            *)
(* Reduces a series of `FST`s and `SND`s applied to a compound pair           *)
(* expression down to the selected subcomponent of the compound pair.         *)
(*                                                                            *)
(* For example:                                                               *)
(*   fst_snd_conv `SND (FST ((x,y),z))`  returns  |- SND (FST ((x,y),z)) = y  *)

let rec fst_snd_conv tm =
  if (is_pair tm) || (is_var tm)
    then eq_refl_conv tm
    else let (f,tm0) = dest_comb tm in
         let th1 = fst_snd_conv tm0 in
         let (tm1,tm2) = dest_pair (eqthm_rhs th1) in
         let ty1 = type_of tm1  and ty2 = type_of tm2 in
         let th = match (const_name f) with
                    "FST" -> fst_thm
                  | "SND" -> snd_thm
                  | _     -> internal_error "fst_snd_conv" in
         let th' = inst_type_rule [(a_ty,ty1);(b_ty,ty2)] th in
         let th2 = list_spec_rule [tm1;tm2] th' in
         eq_trans_rule (mk_comb2_rule f th1) th2;;


(* depair_instns : term -> term * (term * term) list                          *)
(*                                                                            *)
(* Takes a variable structure, and returns a generated variable, for          *)
(* replacing the entire variable structure, and an instantiation list, for    *)
(* replacing individual variables in the variable structure with              *)
(* subcomponents of the generated variable.                                   *)
(*                                                                            *)
(* For example:                                                               *)
(*    depair_instns `((x,y),z)`  returns:                                     *)
(*       ( `_1`,                                                              *)
(*         [(`x`,`FST (FST _1)`); (`y`,`SND (FST _1)`); (`z`,`SND _1`)] )     *)

let rec depair_instns0 (tm,ty) u =
  if (is_pair u)
    then let (u1,u2) = dest_pair u in
         let (ty1,ty2) = dest_prod_type ty in
         let tytheta = [(a_ty,ty1);(b_ty,ty2)] in
         let tm1 = mk_comb (mk_iconst ("FST",tytheta), tm) in
         let tm2 = mk_comb (mk_iconst ("SND",tytheta), tm) in
         (depair_instns0 (tm1,ty1) u1) @ (depair_instns0 (tm2,ty2) u2)
    else [(u,tm)];;

let depair_instns u =
  let ty = type_of u in
  let gv = genvar ty in
  (* .... want 'gv' to avoid names of *all* variables in 'tm' .... *)
  let theta = depair_instns0 (gv,ty) u in
  (gv,theta);;


(* Function definition command *)

(* new_fun_definition : term -> thm                                           *)
(*                                                                            *)
(* This is the definition command for non-recursive functions.  It takes an   *)
(* optionally universally-quantified equality term.  The LHS of the equality  *)
(* must be a variable (called the "main variable") applied to a (potentially  *)
(* empty) series of variable structure arguments, where the main variable     *)
(* must not have the name of an existing constant (unless in benign           *)
(* redefinition), and the arguments must not contain repeated variables.  Any *)
(* free variables or type variables in the RHS must also occur in the LHS.    *)
(*                                                                            *)
(* The resulting theorem defines a new constant with the same name and type   *)
(* as the supplied main variable.  It has no assumptions and its conclusion   *)
(* is an equality universally quantified by all the argument variables, with  *)
(* the new constant replacing the main variable in the LHS.  The theorem      *)
(* quantifies the argument variables in the same order as they are quantified *)
(* in the supplied term, and any variables not quantified in the term are     *)
(* quantified outermost, in the order they occur in the LHS's arguments.  For *)
(* cases of benign redefinition, the "main variable" is allowed to be the     *)
(* existing constant.                                                         *)
(*                                                                            *)
(*      `!xs0. %f u1 u2 .. = t`   (where `u1`, `u2` are variable structures)  *)
(*    --------------------------- [ free vars in `t` must occur in `u1` ..;   *)
(*    |- !xs2 xs1. f u1 u2 .. = t   tyvars in `t` must occur in `f`, `u1` ..; *)
(*                                  no repeated vars in `u1`, .. ]            *)

let new_fun_definition tm =       (* !vs. f u1 u2 .. = t     *)
  let func = "new_fun_definition" in
  let (vs0,tm0) = strip_forall tm in
  let (lhs,rhs) = try1 dest_eq tm0        (func,"Body not an equality") in
  let (f,us) = strip_comb lhs in
  let x = try var_name f  with HolFail _ ->  try const_name f
          with HolFail _ ->
               hol_fail (func,"LHS not a var or a var function application") in
  let (gvs,thetas) = unzip (map depair_instns us) in
  let theta1 = flatten thetas in       (* vi |-> FST/SND (.. (FST/SND gj)..) *)
  let vs = map fst theta1 in
  let () = assert1 (forall is_var vs)      (func,"Function param not a var") in
  let vs_ = bag_subtract vs (setify' term_eq vs) in
  let _ = try assert (is_empty vs_)
          with Assert_failure _ ->
              let x1 = var_name (hd vs_) in
              hol_fail (func, "Function param " ^ quote x1 ^ " is repeated") in
  let vs1 = intersect vs0 vs in   (* originally quantified arg vars *)
  let vs2 = subtract vs vs0 in    (* originally unquantified arg vars *)
 try
  let () = assert0 (cannot get_fun_definition x)     LocalFail in
  let () = assert1 (not (is_const_name x))
                      (func, "Constant name " ^ quote x ^ " already used") in
  let () = assert1 (subset (free_vars rhs) vs)
                                        (func,"RHS has free vars not in LHS") in
  let () = assert1 (subset (term_tyvars rhs) (term_tyvars f))
                                        (func,"RHS has tyvars not in LHS") in
  let tm1 = list_mk_abs (gvs, var_inst theta1 rhs) in
  let th1 = try2 prim_new_const_definition (x,tm1)     func in
                                         (* |- f = (\gv1 gv2 .. . t[theta1]) *)
  let th2 = list_app_beta_rhs_rule th1 gvs in(* |- f g1 g2 .. = t[theta1]    *)
  let theta2 = zip gvs us in                 (* gvi |-> ui   *)
  let th3 = inst_rule theta2 th2 in      (* |- f u1 u2 .. = t[theta1;theta2] *)
  let tm0s = map (var_inst theta2 <* snd) theta1 in
  let th0s = map (eq_sym_rule <* fst_snd_conv) tm0s in
                                             (* |- vi= vi[theta1;theta2]     *)
  let th4 = subs_conv th0s rhs in            (* |- t = t[theta1;theta2]      *)
  let th5 = eq_trans_rule th3 (eq_sym_rule th4) in  (* |- f u1 u2 .. = t     *)
  let th6 = list_gen_rule (vs2 @ vs1) th5 in (* |- !vs2 vs1. f u1 u2 .. = t  *)
  (the_fun_defs := dltree_insert (x,th6) !the_fun_defs;
   th6)
 with LocalFail ->
  (* Benign redefinition *)
  let th' = get_fun_definition x in
  let (vs21',tm0') = strip_forall (concl th') in
  let (lhs',rhs') = dest_eq tm0' in
  let (f',us') = strip_comb lhs' in
  let vs' = flatten (map flatstrip_pair us') in
 try
  let () = assert (length vs' = length vs) in
  let theta = zip vs vs' in
  let rhs_ = var_inst theta rhs in
  let vs21_ = map (var_inst theta) (vs2 @ vs1) in
  let us_ = map (var_inst theta) us in
  let () = assert ((vs21' = vs21_) && (us' = us_) && (alpha_eq rhs' rhs_)) in
  (warn ("Benign redefinition of constant " ^ quote x);
   th')
 with Assert_failure _ ->
         hol_fail (func, "Constant name " ^ quote x ^ " already used");;



(* ** RECURSIVE FUNCTION DEFINITION ** *)


let strip_vararg_comb tm =
  if (is_empty (free_vars tm))
    then (tm,[])
    else strip_comb tm;;

let primrec_theorem_info th =
  let () = assert0 (is_empty (asms th))    LocalFail in
  let (es,tm1) = strip_forall (concl th) in
  let (f,tm2) = dest_exists tm1 in
  let tms2 = flatstrip_conj tm2 in
  let arg_info nxs (n,arg) =
     if (is_comb arg)
       then let (f0,x0) = dest_comb arg in
            let () = assert0 (f0 = f)    LocalFail in
            let () = assert0 (is_var x0)     LocalFail in
            let n0 = try0 (inv_assoc x0) nxs     LocalFail in
            (true,n0)
       else let () = assert0 (is_var arg)    LocalFail in
            let n0 = try0 (inv_assoc arg) nxs    LocalFail in
            (false,n0) in
  let conjunct_info tm =
     let (vs,b) = strip_forall tm in
     let (lhs,rhs) = dest_eq b in
     let (f0,cxs) = dest_comb lhs in
     let () = assert0 (f0 = f) LocalFail in
     let () = assert0 (not (mem f0 vs)) LocalFail in
     let (c,xs) = strip_vararg_comb cxs in
     let () = assert0 (is_empty (free_vars c)) LocalFail in
     let () = assert0 (forall is_var xs) LocalFail in
     let () = assert0 (no_dups xs) LocalFail in
     let nxs = enumerate xs in
     let (e,args) = strip_comb rhs in
     let () = assert0 (is_var e) LocalFail in
     let () = assert0 (not (mem e (f0::vs))) LocalFail in
     let nargs = enumerate args in
     let rhsinfo = map (arg_info nxs) nargs in
     (c,(xs,e,rhsinfo)) in
  let info = map conjunct_info tms2 in
  let cs = map fst info in
  let () = assert0 (no_dups cs) LocalFail in
  (f,info);;

let def_term_info tm =
  let tms = strip_conj tm in
  let conjunct_info tm =
     let (vs0,b) = strip_forall tm in
     let (lhs,rhs) = dest_eq b in
     let (g,args) = strip_comb lhs in
     let () = assert0 (is_var g) LocalFail in
     let (ys1,args1) = cut_while is_var args in
     let (cxs,ys2) = try0 hd_tl args1 LocalFail in
     let () = assert0 (forall is_var ys2) LocalFail in
     let ys = ys1 @ ys2 in
     let n = length args in
     let i = length ys1 + 1 in
     let (c,xs) = strip_vararg_comb cxs in
     let nxs = enumerate xs in
     let () = assert0 (forall is_var xs) LocalFail in
     let vs = xs @ ys in
     let () = assert0 (no_dups vs) LocalFail in
     let () = assert0 (subset (free_vars rhs) (g::vs)) LocalFail in
     let p tm = fst (strip_comb tm) = g in
     let tms0 = find_subterms p rhs in
     let g_app_info tm =
        let (_,args) = strip_comb tm in
        let () = assert0 (length args = n) LocalFail in
        let (x,args0) = extract i args in
        let j = inv_assoc x nxs in
        let () = assert0 (mem x xs) LocalFail in
        let fvs = list_free_vars args0 in
        let () = assert0 (disjoint fvs xs) LocalFail in
        (j,args0) in
     let xargs = map g_app_info tms0 in
     ((g,i),(c,(xs,ys,vs0,xargs,rhs))) in
  let (gis,info) = unzip (map conjunct_info tms) in
  let cns = map (fun (c,(_,ys,_,_,_)) -> (c, length ys)) info in
  let (cs,ns) = unzip cns in
  let () = assert0 (no_dups cs) LocalFail in
  let (n,ns0) = hd_tl ns in
  let () = assert0 (forall (fun n0 -> n0 = n) ns0) LocalFail in
  let ((g,i),gis0) = hd_tl gis in
  let () = assert0 (forall (fun (g0,i0) -> (g0 = g) && (i0 = i)) gis0)
                                                                  LocalFail in
  ((g,i),info);;


let create_primrec_instns (f,conjinfoA) ((g,i),conjinfoB) =
  let cnsA = map (fun (c,(xs,_,_)) -> (c, length xs)) conjinfoA in
  let cnsB = map (fun (c,(xs,_,_,_,_)) -> (c, length xs)) conjinfoB in
  let () = assert0 (subset cnsB cnsA) LocalFail in
  let foo (c,(xsB,ysB,vsB,xargsB,rhsB)) =
     let (xsA,eA,rhsinfoA) = assoc c conjinfoA in
     ((c,xsA,xsB,ysB),(eA,rhsinfoA,xargsB,rhsB)) in
  let conjinfo = map foo conjinfoB in
  (* Create 'x' instns for each conjunct *)
  let xthetas = map (fun ((c,xsA,xsB,_),_) -> (c, zip xsA xsB)) conjinfo in
  (* Create 'f' instn *)
  let (_,_,_,ysB) = fst (hd conjinfo) in
  let (tys1,ty2) = strip_fun_type (type_of g) in
  let (tyx,tys0) = extract i tys1 in
  let tyz = list_mk_fun_type (tys0,ty2) in
  let x = variant (g::ysB) (mk_var ("x",tyx)) in
  let ty' = list_mk_fun_type (tyx::tys0,ty2) in
  let tytheta = type_match (type_of f) ty' in
  let f' = tyvar_inst tytheta f in
  let f'' = list_mk_abs (inject i x ysB, list_mk_comb (f', x::ysB)) in
  (* Create 'e' instns *)
  let mk_e_fn ((c,xsA,xsB,ysB),(eA,rhsinfoA,xargsB,rhsB)) =
     let m = length xsB in
     let znames = map (fun n -> "z" ^ string_of_int n) (up_to 1 m) in
     let zs = list_variant (g::(xsB @ ysB))
                           (map (fun n -> mk_var (n,tyz)) znames) in
     let foo (b,n) = if b then el n zs
                          else el n xsB in
     let vs = (map foo rhsinfoA) @ ysB in
     let make_gapp_inst (n,ys) =
        let x0 = el n xsB in
        let z = el n zs in
        let tm = list_mk_comb (g, inject i x0 ys) in
        let tm' = list_mk_comb (z, ys) in
        (tm,tm') in
     let theta1 = map make_gapp_inst xargsB in
     let e0 = subst theta1 rhsB in
     let e' = list_mk_abs (vs,e0) in
     (tyvar_inst tytheta eA, e') in
  let etheta = map mk_e_fn conjinfo in
  (tytheta,(f',f''),etheta,xthetas);;


let new_recursive_fun_definition th tm =
  let infoA = primrec_theorem_info th in
  let infoB = def_term_info tm in
  let (tytheta,(f,f'),etheta,xthetas) = create_primrec_instns infoA infoB in
  let th1 = inst_type_rule tytheta th in
  let th2 = spec_all_rule th1 in
  let th3 = inst_rule etheta th2 in
  let tm4 = (snd <* dest_exists <* concl) th3 in
  let th4 = assume_rule tm4 in
  let ths4 = flat_conjuncts_rule th4 in
  let (g,i) = fst infoB in    (* know 'g' doesn't clash coz comes from 'tm' *)
  let foo (n,th) =
     let (c,(xsB,ysB,vsB,_,_)) = (el n <* snd) infoB in
     let th1 = spec_all_rule th in
     let th2 = inst_rule (assoc c xthetas) th1 in
     let th3 = foldl mk_comb1_rule th2 ysB in
     let (e,args) = (strip_vararg_comb <* eq_rhs <* concl) th3 in
     let th4 = list_app_beta_rhs_rule (eq_refl_conv e) args in
     let tm4 = eq_rhs (concl th4) in
     let tms5 = find_subterms (fun tm -> fst (strip_comb tm) = f) tm4 in
     let foo (x,tms) =
        let tms' = inject i x tms in
        list_app_beta_rhs_rule (eq_refl_conv f') tms' in
     let ths5 = map (eq_sym_rule <* foo <* hd_tl <* snd <* strip_comb) tms5 in
     let th5 = subs_conv ths5 tm4 in
     let tm6 = list_mk_comb (c,xsB) in
     let th6 = foo (tm6,ysB) in
     let th7 = list_eq_trans_rule [th6; th3; th4; th5] in
     let vs = foldr insert (xsB@ysB) vsB in
     list_gen_rule vs th7 in
  let ths5 = map foo (enumerate ths4) in
  let th5 = foldr1 conj_rule ths5 in
  let tm6 = mk_exists (g, subst [(f',g)] (concl th5)) in
  let th6 = exists_rule (tm6, f') th5 in
  let th7 = choose_rule (f, th3) th6 in
  new_const_specification ([var_name g],th7);;


end;;
