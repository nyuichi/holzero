(* ========================================================================== *)
(* BOOLEANS CLASSICAL (HOL Zero)                                              *)
(* - Derived theorems/rules for predicate logic relying on Axiom of Choice    *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2016                            *)
(* ========================================================================== *)


module BoolClass : BoolClass_sig = struct


(* This module derives further predicate logic theorems and inference rules.  *)
(* Unlike all preceding derivations, these all use the Axiom of Choice (i.e.  *)
(* 'select_ax'), and thus could be considered as classical logic.  However,   *)
(* note that some of these (such as 'exists_rule') are actually derivable in  *)
(* intuitionistic logic if an alternative definition of existential           *)
(* quantification is used (as in HOL Light).                                  *)


open Equal;;
open EqCong;;
open Bool;;
open BoolAlg;;



(* select_rule : thm -> thm                                                   *)
(*                                                                            *)
(* This is the existential selection rule.  It strips off the existential     *)
(* quantifier from the supplied theorem, and replaces each occurrence of the  *)
(* binding variable in the body with the selection operator applied to the    *)
(* original body (with the same binding variable).                            *)
(*                                                                            *)
(*       A |- ?x. p                                                           *)
(*    ----------------                                                        *)
(*    A |- p[(@x.p)/x]                                                        *)

let select_rule th =           (* A |- ?x. p  *)
 try
  let (v,p) = dest_exists (concl th) in
  let tm0 = mk_abs (v,p) in
  let ty = type_of v in
  let th1 = list_spec_rule [tm0;v] (inst_type_rule [(a_ty,ty)] select_ax) in
                                       (* |- (\x. p) x ==> (\x. p) (@x. p)   *)
  let (tm1,tm2) = dest_imp (concl th1) in
  let th2 = beta_conv tm1 in           (* |- (\x. p) x <=> p                 *)
  let th3 = beta_conv tm2 in           (* |- (\x. p) (@x. p) <=> p[(@x.p)/x] *)
  let th4 = list_imp_trans_rule [eq_imp_rule2 th2; th1; eq_imp_rule1 th3] in
                                       (* |- p ==> p[(@x.p)/x]               *)
  let th5 = undisch_rule th4 in        (* p |- p[(@x.p)/x]                   *)
  choose_rule (v,th) th5               (* A |- p[(@x.p)/x]                   *)
 with HolFail _ ->
  let func = "select_rule" in
  let () = assert1 (is_exists (concl th))      (func,"Not an existential") in
  internal_error func;;


(* exists_rule : term * term -> thm -> thm                                    *)
(*                                                                            *)
(* This is the existential introduction rule.  It takes an existential term,  *)
(* a witness term and a theorem, where the theorem's conclusion is the body   *)
(* of the existential term but with the witness term replacing occurrences of *)
(* its binding variable.  It returns a theorem stating that the supplied      *)
(* existential term holds, under the same assumptions as the supplied         *)
(* theorem.                                                                   *)
(*                                                                            *)
(*    `?x. p`   `t`   A |- p[t/x]                                             *)
(*    ---------------------------                                             *)
(*            A |- ?x. p                                                      *)

let exists_rule (tm1,tm2) th =       (* ?x. p    t    A |- p[t/x]   *)
 try
  let (v,p) = dest_exists tm1 in
  let ty = type_of v in
  let tm0 = mk_abs (v,p) in
  let th1 = beta_conv (mk_comb (tm0,tm2)) in   (* |- (\x. p) t <=> p[t/x]    *)
  let th2 = eq_mp_rule (eq_sym_rule th1) th in (* A |- (\x. p) t             *)
  let th3 = list_spec_rule [tm0;tm2] (inst_type_rule [(a_ty,ty)] select_ax) in
                                   (* |- (\x. p) t ==> (\x. p) ((@) (\x. p)) *)
  let th4 = mp_rule th3 th2 in                 (* A |- (\x. p) ((@) (\x. p)) *)
  let th5 = app_beta_rhs_rule (inst_type_rule [(a_ty,ty)] exists_def) tm0 in
                                   (* |- (?x. p) <=> (\x. p) ((@) (\x. p))   *)
  eq_mp_rule (eq_sym_rule th5) th4             (* A |- (?x. p)               *)
 with HolFail _ ->
  let func = "exists_rule" in
  let (v,p) = try1  dest_exists tm1       (func,"Arg 1 not an existential") in
  let () = assert1 (same_types tm2 v)
                         (func,"Witness term's type not equal to \
                                existential term's binding var type") in
  let () = assert1 (concl th = var_inst [(v,tm2)] p)
           (func,"Supplied theorem's conclusion is not existential term's body \
                  with binding var occurrences replaced with witness term") in
  internal_error func;;


(* select_eq_thm                                                              *)
(*                                                                            *)
(*    |- !(a:'a). (@x. x = a) = a                                             *)

let select_eq_thm = save_thm ("select_eq_thm",
  let a = `a:'a` in
  gen_rule a
   (select_rule
     (* |- ?x. x = a      *)
     (exists_rule (`?(x:'a).x=a`,a) (eq_refl_conv a)) )
);;


(* exists_dist_disj_thm                                                       *)
(*                                                                            *)
(*    |- !P Q. (?x. P x \/ Q x) <=> (?x. P x) \/ (?x. Q x)                    *)

let exists_dist_disj_thm = save_thm ("exists_dist_disj_thm",
  let px = `(P:'a->bool) x` and qx = `(Q:'a->bool) x` and x = `x:'a`  in
  let tm1 = `?(x:'a). P x` and tm2 = `?(x:'a). Q x` in
  list_gen_rule [`P:'a->bool`;`Q:'a->bool`]
    (deduct_antisym_rule
      (* (?x. P x) \/ (?x. Q x) |- ?x. P x \/ Q x      *)
      (disj_cases_rule (assume_rule `(?(x:'a). P x) \/ (?(x:'a). Q x)`)
        (* ?x. P x |- ?x. P x \/ Q x                     *)
        (choose_rule (x, assume_rule tm1)
          (exists_rule (`?(x:'a). P x \/ Q x`, x)
            (disj1_rule (assume_rule px) qx) ))
        (* ?x. Q x |- ?x. P x \/ Q x                     *)
        (choose_rule (x, assume_rule tm2)
          (exists_rule (`?(x:'a). P x \/ Q x`, x)
            (disj2_rule px (assume_rule qx)) )))
      (* ?x. P x \/ Q x |- (?x. P x) \/ (?x. Q x)      *)
      (choose_rule (x, assume_rule `?(x:'a). P x \/ Q x`)
        (* P x \/ Q x |- (?x. P x) \/ (?x. Q x)          *)
        (disj_cases_rule (assume_rule `P (x:'a) \/ Q x`)
          (* P x |- (?x. P x) \/ (?x. Q x)                 *)
          (disj1_rule (exists_rule (tm1,x) (assume_rule px)) tm2)
          (* Q x |- (?x. P x) \/ (?x. Q x)                 *)
          (disj2_rule tm1 (exists_rule (tm2,x) (assume_rule qx))) )))
);;


(* exists_one_point_thm                                                       *)
(*                                                                            *)
(*    |- !P a. (?x. x = a /\ P x) <=> P a                                     *)

let exists_one_point_thm = save_thm ("exists_one_point_thm",
  let tm = `?(x:'a). x = a /\ P x` in
  let s1 = assume_rule `(x:'a)=a /\ P x` in
  gen_rule `P:'a->bool`
   (gen_rule `a:'a`
     (deduct_antisym_rule
       (exists_rule (tm, `a:'a`)
         (conj_rule (eq_refl_conv `a:'a`) (assume_rule `(P:'a->bool) a`)))
       (choose_rule (`x:'a`, assume_rule tm)
         (eq_mp_rule (mk_comb2_rule `P:'a->bool` (conjunct1_rule s1))
                (conjunct2_rule s1)) )))
);;


(* exists_value_thm                                                           *)
(*                                                                            *)
(*    |- !x. (?y. y = x)                                                      *)

let exists_value_thm = save_thm ("exists_value_thm",
  let x = `x:'a` in
  gen_rule x
   (exists_rule (`?(y:'a).y=x`, x) (eq_refl_conv x))
);;


(* exists_null_thm                                                            *)
(*                                                                            *)
(*    |- !t. (?x. t) <=> t                                                    *)

let exists_null_thm = save_thm ("exists_null_thm",
  let s1 = assume_rule `t:bool` in
  gen_rule `t:bool`
   (deduct_antisym_rule
     (exists_rule (`?(x:'a).t`, `y:'a`) s1)
     (choose_rule (`x:'a`, assume_rule `?(x:'a).t`) s1))
);;


(* uexists_thm1                                                               *)
(*                                                                            *)
(*    |- !P. (?!x. P x) <=> (?x. P x /\ (!y. P y ==> y = x))                  *)

let uexists_thm1 = save_thm ("uexists_thm1",
  let p = `P:'a->bool` in
  gen_rule p
   (bspec_rule `\x. (P:'a->bool) x`
     (gen_rule p (app_beta_rhs_rule uexists_def p)) )
);;


(* uexists_thm2                                                               *)
(*                                                                            *)
(*    |- !P. (?!x. P x) <=> (?x. !y. P y <=> x = y)                           *)

let uexists_thm2 = save_thm ("uexists_thm2",
  let y = `y:'a`  and x = `x:'a` in
  let p = `P:'a->bool` in
  let tm1 = `(P:'a->bool) y` in
  let s1 = assume_rule `!(y:'a). P y <=> x = y` in
  let s2 = assume_rule `P x /\ (!(y:'a). P y ==> y = x)` in
  gen_rule p
   (eq_trans_rule
     (spec_rule p uexists_thm1)
     (mk_exists_rule x
       (deduct_antisym_rule
         (conj_rule
           (eq_mp_rule (eq_sym_rule (spec_rule x s1)) (eq_refl_conv x))
           (gen_rule y
             (disch_rule tm1
               (eq_sym_rule (eq_mp_rule (spec_rule y s1) (assume_rule tm1))) )))
         (gen_rule y
           (deduct_antisym_rule
             (eq_mp_rule
               (mk_comb2_rule p (assume_rule `(x:'a) = y`))
               (conjunct1_rule s2) )
             (eq_sym_rule
               (undisch_rule (spec_rule y (conjunct2_rule s2))) ))) )))
);;


(* uexists_thm3                                                               *)
(*                                                                            *)
(*    |- !P. (?!x. P x) <=> (?x. P x) /\ (!x x'. P x /\ P x' ==> x = x')      *)

let uexists_thm3 = save_thm ("uexists_thm3",
  let x = `x:'a`  and x' = `x':'a`  and x'' = `x'':'a`  and y = `y:'a` in
  let p = `(P:'a->bool)` in
  let tm1 = `(P:'a->bool) x` in
  let tm2 = `(P:'a->bool) y` in
  let th1 = assume_rule `(?(x:'a). P x) /\ (!x x'. P x /\ P x' ==> x = x')` in
  let th2 = assume_rule `P (x:'a) /\ (!y. P y ==> y = x)` in
  gen_rule p
   (eq_trans_rule
     (spec_rule p uexists_thm1)
     (deduct_antisym_rule
       (choose_rule (x, conjunct1_rule th1)
         (exists_rule (`?(x:'a). P x /\ (!y. P y ==> y = x)`, x)
           (conj_rule
             (assume_rule tm1)
             (gen_rule y
               (disch_rule tm2
                 (mp_rule (list_spec_rule [y;x] (conjunct2_rule th1))
                     (conj_rule (assume_rule tm2) (assume_rule tm1)) ))))))
       (choose_rule (x, assume_rule `?(x:'a). P x /\ (!y. P y ==> y = x)`)
         (conj_rule
           (exists_rule (`?(x:'a). P x`, x) (conjunct1_rule th2))
           (list_gen_rule [x';x'']
             (disch_rule `P (x':'a) /\ P x''`
               (prove_asm_rule
                 (conjunct1_rule (assume_rule `P (x':'a) /\ P x''`))
                 (prove_asm_rule
                   (conjunct2_rule (assume_rule `P (x':'a) /\ P x''`))
                   (eq_trans_rule
                     (undisch_rule (spec_rule x' (conjunct2_rule th2)))
                     (eq_sym_rule
                       (undisch_rule (spec_rule x'' (conjunct2_rule th2))))
       )))))))
  ))
);;


(* uexists_one_point_thm                                                      *)
(*                                                                            *)
(*    |- !P a. (?!x. x = a /\ P x) <=> P a                                    *)

let uexists_one_point_thm = save_thm ("uexists_one_point_thm",
  let x' = `x':'a`  and x'' = `x'':'a`  and a = `a:'a` in
  let p = `(P:'a->bool)` in
  let tm = `(x' = (a:'a) /\ P x') /\ x'' = a /\ P x''` in
  let th = assume_rule tm in
  list_gen_rule [p;a]
   (list_eq_trans_rule
      [ bspec_rule `\(x:'a). x = a /\ P x` uexists_thm3;
        mk_conj_rule
         (list_spec_rule [p;a] exists_one_point_thm)
         (eqt_intro_rule
           (list_gen_rule [x';x'']
             (disch_rule tm
               (eq_trans_rule
                 (conjunct1_rule (conjunct1_rule th))
                 (eq_sym_rule (conjunct1_rule (conjunct2_rule th))) ))));
        spec_rule `(P:'a->bool) a` conj_id_thm ])
);;


(* skolem_thm                                                                 *)
(*                                                                            *)
(*    |- !P. (!x. ?y. P x y) <=> (?f. !x. P x (f x))                          *)

let skolem_thm = save_thm ("skolem_thm",
  gen_rule `P:'a->'b->bool`
   (deduct_antisym_rule
     (choose_rule (`f:'a->'b`, assume_rule `?f. !x. (P:'a->'b->bool) x (f x)`)
       (gen_rule `x:'a`
         (exists_rule (`?(y:'b). P (x:'a) y`,`(f:'a->'b) x`)
             (spec_rule `x:'a` (assume_rule `!x. (P:'a->'b->bool) x (f x)`)) )))
     (exists_rule
             (`?f. !x. (P:'a->'b->bool) x (f x)`, `\(x:'a). @(y:'b). P x y`)
       (gen_rule `x:'a`
         (eq_mp_rule
           (mk_comb2_rule `(P:'a->'b->bool) x`
             (eq_sym_rule (beta_conv `(\(x:'a). @(y:'b). P x y) x`)))
           (select_rule
             (spec_rule `x:'a` (assume_rule `!(x:'a). ?(y:'b). P x y`)) )))))
);;


(* unique_skolem_thm                                                          *)
(*                                                                            *)
(*    |- !P. (!x. ?!y. P x y) <=> (?f. !x y. P x y <=> f x = y)               *)

let unique_skolem_thm = save_thm ("unique_skolem_thm",
  let tm1 = `?f. !(x:'a) (y:'b). P x y <=> f x = y` in
  gen_rule `P:'a->'b->bool`
    (eq_mp_rule
      (eq_sym_rule
        (mk_eq1_rule
          (eq_trans_rule
            (mk_forall_rule `x:'a`
              (bspec_rule `\y. (P:'a->'b->bool) x y`
                (inst_type_rule [(a_ty,b_ty)] uexists_thm2) ))
            (bspec_rule `\(x:'a) (y:'b). !y'. P x y' <=> y = y'` skolem_thm) )
          tm1 ))
      (eq_refl_conv tm1) )
);;


(* not_dist_exists_thm : thm                                                  *)
(*                                                                            *)
(*    |- !P. ~ (?x. P x) <=> (!x. ~ P x)                                      *)

let not_dist_exists_thm = save_thm ("not_dist_exists_thm",
  let x = `x:'a` and p = `P:'a->bool` in
  let px = mk_comb (p,x) in
  (* |- !P. ~ (?x. P x) <=> (!x. ~ P x)       *)
  gen_rule p
    (deduct_antisym_rule
      (* !x. ~ P x |- ~ (?x. P x)         *)
      (not_intro_rule
        (disch_rule `?(x:'a). P x`
          (* !x. ~ P x, ?x. P x |- false      *)
          (choose_rule (x, assume_rule `?(x:'a). P x`)
            (* !x. ~ P x, P x |- false          *)
            (undisch_rule
              (not_elim_rule
                (spec_rule x (assume_rule `!(x:'a). ~ P x`)) )))))
      (* ~ (?x. P x) |- !x. ~ P x         *)
      (gen_rule x
        (* ~ (?x. P x) |- ~ P x             *)
        (deduct_contrapos_rule px
          (* P x |- ?x. P x                   *)
          (exists_rule (`?(x:'a). P x`, x) (assume_rule px)) )))
);;


(* excluded_middle_thm : thm                                                  *)
(*                                                                            *)
(*    |- !p. p \/ ~p                                                          *)
(*                                                                            *)
(* The proof is roughly based on that from Radu Diaconescu (1975), but has    *)
(* been simplified.                                                           *)

let excluded_middle_thm = save_thm ("excluded_middle_thm",
  let p = mk_var ("p",bool_ty) in
  let th1 = assume_rule p in                    (* p |- p           *)
  let th2 = disj1_rule th1 (mk_not p) in        (* p |- p \/ ~ p    *)
  gen_rule p
   (* |- p \/ ~ p                  *)
   (disj_cases_rule
     (* |- ~ (@x. ~ x \/ p) \/ p             *)
     (select_rule
       (* |- ?x. ~ x \/ p                      *)
       (exists_rule (`?x. ~ x \/ p`, `false`)
         (disj1_rule (eqt_elim_rule not_false_thm) p) ))
     (* ~ (@x. ~ x \/ p) |- p \/ ~ p         *)
     (disj_cases_rule
       (* |- (@x. x \/ p) \/ p                 *)
       (select_rule
         (* |- ?x. x \/ p                        *)
         (exists_rule (`?x. x \/ p`, `true`)
           (disj1_rule truth_thm p) ))
       (* @x. x \/ p, ~ (@x. ~ x \/ p) |- p \/ ~ p   *)
       (disj2_rule p
         (* @x. x \/ p, ~ (@x. ~ x \/ p) |- ~ p    *)
         (deduct_contrapos_rule p
           (* @x. x \/ p, p |- @x. ~ x \/ p          *)
           (eq_mp_rule
             (* p |- (@x. x \/ p) <=> (@x. ~ x \/ p)   *)
             (mk_select_rule `x:bool`
               (deduct_antisym_rule
                 (disj2_rule `x:bool` th1)
                 (disj2_rule `~x` th1) ))
             (assume_rule `@x. x \/ p`) )))
       (* p |- p \/ ~ p                          *)
       th2 )
     th2 )
);;


(* bool_cases_thm : thm                                                       *)
(*                                                                            *)
(*    |- !p. (p <=> true) \/ (p <=> false)                                    *)

let bool_cases_thm = save_thm ("bool_cases_thm",
  let p = mk_var ("p",bool_ty) in
  (* |- !p. (p <=> true) \/ (p <=> false)    *)
  gen_rule p
   (disj_cases_rule
     (* |- p \/ ~p                               *)
     (spec_rule p excluded_middle_thm)
     (* p |- (p <=> true) \/ (p <=> false)       *)
     (disj1_rule
       (eqt_intro_rule (assume_rule p))
       `p <=> false`)
     (* ~p |- (p <=> true) \/ (p <=> false)      *)
     (disj2_rule `p <=> true`
       (eqf_intro_rule (assume_rule `~ p`)) ))
);;


(* ccontr_rule : term -> thm -> thm                                           *)
(*                                                                            *)
(* This is the classical contradiction rule.  It takes a boolean term and a   *)
(* theorem with falsity as its conclusion.  It returns a theorem with the     *)
(* supplied term as its conclusion, and with the same assumptions as the      *)
(* supplied theorem but with the logical negation of the supplied term        *)
(* removed.  Note that the logical negation of the supplied term does not     *)
(* have to be in the supplied theorem's assumptions for the rule to succeed.  *)
(*                                                                            *)
(*    `p`   A |- false                                                        *)
(*    ----------------                                                        *)
(*      A\{~ p} |- p                                                          *)

let ccontr_lemma =
  let p_ = `p_:bool` in
  (* |- (~ p_ ==> false) ==> p_  *)
  disch_rule `~ p_ ==> false`
    (disj_cases_rule
      (* |- p_ \/ ~ p_              *)
      (spec_rule p_ excluded_middle_thm)
      (* p_ |- p_                   *)
      (assume_rule p_)
      (* ~ p_ ==> false, ~ p_ |- p_   *)
      (contr_rule p_
        (undisch_rule (assume_rule `~ p_ ==> false`)) ));;

let ccontr_rule tm th =            (* p    A |- false   *)
 try
  let p_ = mk_var ("p_",bool_ty) in
  let th1 = inst_rule [(p_,tm)] ccontr_lemma in  (* |- (~ p ==> false) ==> p  *)
  let th2 = disch_rule (mk_not tm) th in         (* A\{~ p} |- ~ p ==> false  *)
  mp_rule th1 th2                                (* A\{~ p} |- p              *)
 with HolFail _ ->
  let func = "ccontr_rule" in
  let () = assert1 (is_bool_term tm)          (func,"Arg 1 not boolean") in
  let () = assert1 (concl th = false_tm)      (func,"Arg 2 not `false`") in
  internal_error func;;


(* not_dneg_thm : thm                                                         *)
(*                                                                            *)
(*    |- !p. ~ ~ p <=> p                                                      *)

let not_dneg_thm = save_thm ("not_dneg_thm",
  let p = `p:bool` in
  (* |- !p. ~ ~ p <=> p        *)
  gen_rule p
   (deduct_antisym_rule
     (* p |- ~ ~ p             *)
     (eqf_elim_rule
       (* p |- ~ p <=> false     *)
       (eq_trans_rule
         (* p |- ~ p <=> ~ true    *)
         (mk_not_rule (eqt_intro_rule (assume_rule p)))
         not_true_thm ))
     (* ~ ~ p |- p                 *)
     (ccontr_rule `p:bool`
       (* ~ ~ p , ~ p |- F           *)
       (undisch_rule (not_elim_rule (assume_rule `~ ~ p`))) ))
);;


(* imp_disj_thm                                                               *)
(*                                                                            *)
(*    |- !p q. (p ==> q) <=> (~ p \/ q)                                       *)

let imp_disj_thm = save_thm ("imp_disj_thm",
  let p = `p:bool` and q = `q:bool`  in
  list_gen_rule [p;q]
    (deduct_antisym_rule
      (* ~ p \/ q |- p ==> q                  *)
      (disj_cases_rule (assume_rule `~ p \/ q`)
        (* ~ p |- p ==> q                       *)
        (imp_trans_rule
          (not_elim_rule (assume_rule `~ p`))
          (spec_rule q imp_left_zero_thm) )
        (* q |- p ==> q                         *)
        (disch_rule p (assume_rule q)) )
      (* p ==> q |- ~ p \/ q                  *)
      (disj_cases_rule (spec_rule p excluded_middle_thm)
        (disj2_rule `~ p`
          (undisch_rule (assume_rule `p ==> q`)) )
        (disj1_rule (assume_rule `~ p`) q) ))
);;


(* not_dist_conj_thm : thm                                                    *)
(*                                                                            *)
(*    |- !p q. ~ (p /\ q) <=> ~ p \/ ~ q                                      *)

let not_dist_conj_thm = save_thm ("not_dist_conj_thm",
  let p = `p:bool` and q = `q:bool`  in
  list_gen_rule [p;q]
    (deduct_antisym_rule
      (* ~ p \/ ~ q |- ~ (p /\ q)          *)
      (disj_cases_rule (assume_rule `~ p \/ ~ q`)
        (* ~ p |- ~ (p /\ q)                 *)
        (deduct_contrapos_rule `p /\ q`
          (conjunct1_rule (assume_rule `p /\ q`)) )
        (* ~ q |- ~ (p /\ q)                 *)
        (deduct_contrapos_rule `p /\ q`
          (conjunct2_rule (assume_rule `p /\ q`)) ))
      (* ~ (p /\ q) |- ~ p \/ ~ q          *)
      (disj_cases_rule (spec_rule p excluded_middle_thm)
        (* ~ (p /\ q), p |- ~ p \/ ~ q       *)
        (disj2_rule `~ p`
          (* ~ (p /\ q), p |- ~ q              *)
          (deduct_contrapos_rule q
            (conj_rule (assume_rule p) (assume_rule q)) ))
        (* ~ p |- ~ p \/ ~ q                 *)
        (disj1_rule (assume_rule `~ p`) `~ q`) ))
);;


(* not_dist_forall_thm : thm                                                  *)
(*                                                                            *)
(*    |- !P. ~ (!x. P x) <=> (?x. ~ P x)                                      *)

let not_dist_forall_thm = save_thm ("not_dist_forall_thm",
  let x = `x:'a` and  p = `P:'a->bool` in
  let px = mk_comb (p,x) in
  (* |- ~ (!(x:'a). P x) <=> (?x. ~ P x)       *)
  gen_rule p
    (eq_trans_rule
      (* |- ~ (!(x:'a). P x) <=> ~ ~ (?x. ~ P x)   *)
      (eq_sym_rule
        (mk_not_rule
          (* |- ~ (?x. ~ P x) <=> (!x. P x)            *)
          (eq_trans_rule
            (* |- ~ (?x. ~ P x) <=> (!x. ~ ~ P x)        *)
            (bspec_rule `\(x:'a). ~ P x` not_dist_exists_thm)
            (* |- (!x. ~ ~ P x) <=> (!x. P x)            *)
            (mk_forall_rule x
              (spec_rule px not_dneg_thm) ))))
      (* |- ~ ~ (?(x:'a). ~ P x) <=> (?x. ~ P x)   *)
      (spec_rule `(?(x:'a). ~ P x)` not_dneg_thm) )
);;


(* cond_true_thm                                                              *)
(*                                                                            *)
(*    |- !t1 t2. (if true then t1 else t2) = t1                               *)

let cond_true_thm = save_thm ("cond_true_thm",
  let t1 = `t1:'a` and t2 = `t2:'a` in
  let xt1 = `(x:'a) = t1` and xt2 = `(x:'a) = t2` in
  list_gen_rule [t1;t2]
    (list_eq_trans_rule
       [ (* |- (if true then t1 else t2)                               *)
         (*            = (@(x:'a). ((true <=> true) ==> x = t1) /\     *)
         (*                        ((true <=> false) ==> x = t2))      *)
         list_app_beta_rhs_rule cond_def [`true`;t1;t2];
         (* |- (@(x:'a). ((true <=> true) ==> x = t1) /\               *)
         (*              ((true <=> false) ==> x = t2))                *)
         (*    = (@x. x = t1)                                          *)
         mk_select_rule `x:'a`
          (eq_trans_rule
            (mk_conj_rule
              (eq_trans_rule
                (mk_imp1_rule (eqt_intro_rule (eq_refl_conv `true`)) xt1)
                (spec_rule xt1 imp_left_id_thm))
              (eq_trans_rule
                (mk_imp1_rule (eqf_intro_rule true_not_eq_false_thm) xt2)
                (eqt_intro_rule (spec_rule xt2 imp_left_zero_thm)) ))
            (spec_rule xt1 conj_id_thm) );
         (* |- (@x. x = t2) = t2                                       *)
         spec_rule t1 select_eq_thm ])
);;


(* cond_false_thm                                                             *)
(*                                                                            *)
(*    |- !t1 t2. (if false then t1 else t2) = t2                              *)

let cond_false_thm = save_thm ("cond_false_thm",
  let t1 = `t1:'a` and t2 = `t2:'a` in
  let xt1 = `(x:'a) = t1` and xt2 = `(x:'a) = t2` in
  list_gen_rule [t1;t2]
    (list_eq_trans_rule
       [ (* |- (if false then t1 else t2)                              *)
         (*             = (@(x:'a). ((false <=> true) ==> x = t1) /\   *)
         (*                         ((false <=> false) ==> x = t2))    *)
         list_app_beta_rhs_rule cond_def [`false`;t1;t2];
         (* |- (@(x:'a). ((false <=> true) ==> x = t1) /\              *)
         (*              ((false <=> false) ==> x = t2))               *)
         (*    = (@x. x = t2)                                          *)
         mk_select_rule `x:'a`
          (list_eq_trans_rule
             [ mk_conj_rule
                (eq_trans_rule
                  (mk_imp1_rule
                    (eq_trans_rule (eq_sym_conv `false <=> true`)
                                   (eqf_intro_rule true_not_eq_false_thm))
                    xt1 )
                  (eqt_intro_rule (spec_rule xt1 imp_left_zero_thm)) )
                (eq_trans_rule
                  (mk_imp1_rule (eqt_intro_rule (eq_refl_conv `false`)) xt2)
                  (spec_rule xt2 imp_left_id_thm) );
               list_spec_rule [`true`;xt2] conj_comm_thm;
               spec_rule xt2 conj_id_thm ] );
         (* |- (@x. x = t2) = t2                                       *)
         spec_rule t2 select_eq_thm ])
);;


(* cond_idem_thm                                                              *)
(*                                                                            *)
(*    |- !p t. (if p then t else t) = t                                       *)

let cond_idem_thm = save_thm ("cond_idem_thm",
  let p = `p:bool` and t = `t:'a` in
  let tm = `if p then (t:'a) else t` in
  list_gen_rule [p;t]
   (disj_cases_rule (spec_rule p bool_cases_thm)
     (* p <=> true |- (if p then t else t) = t    *)
     (eq_trans_rule
       (subs_conv [assume_rule `p <=> true`] tm)
       (list_spec_rule [t;t] cond_true_thm) )
     (* p <=> false |- (if p then t else t) = t   *)
     (eq_trans_rule
       (subs_conv [assume_rule `p <=> false`] tm)
       (list_spec_rule [t;t] cond_false_thm) ))
);;


(* cond_not_thm                                                               *)
(*                                                                            *)
(*    |- !p t1 t2. (if ~ p then t1 else t2) = (if p then t2 else t1)          *)

let cond_not_thm = save_thm ("cond_not_thm",
  let p = `p:bool` and t1 = `t1:'a` and t2 = `t2:'a` in
  let tma = `if ~ p then (t1:'a) else t2` in
  let tmb = `if p then (t2:'a) else t1` in
  let th1 = assume_rule `~ p <=> true` in
  let th2 = assume_rule `~ p <=> false` in
  list_gen_rule [p;t1;t2]
   (disj_cases_rule (spec_rule `~ p` bool_cases_thm)
     (* ~ p <=> true |- (if ~ p then t1 else t2) = (if p then t2 else t1)   *)
     (list_eq_trans_rule
        [ subs_conv [th1] tma;
          list_spec_rule [t1;t2] cond_true_thm;
          eq_sym_rule (list_spec_rule [t2;t1] cond_false_thm);
          eq_sym_rule (subs_conv [eqf_intro_rule (eqt_elim_rule th1)] tmb) ])
     (* ~ p <=> false |- (if ~ p then t1 else t2) = (if p then t2 else t1)  *)
     (list_eq_trans_rule
        [ subs_conv [th2] tma;
          list_spec_rule [t1;t2] cond_false_thm;
          eq_sym_rule (list_spec_rule [t2;t1] cond_true_thm);
          let th3 = eq_mp_rule (spec_rule p not_dneg_thm) (eqf_elim_rule th2) in
          eq_sym_rule (subs_conv [eqt_intro_rule th3] tmb) ]))
);;


end;;
