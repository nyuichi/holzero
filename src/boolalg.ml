(* ========================================================================== *)
(* BOOLEAN ALGEBRA (HOL Zero)                                                 *)
(* - Derived algebraic theorems for predicate logic                           *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2015                            *)
(* ========================================================================== *)


module BoolAlg : BoolAlg_sig = struct


(* This module proves various algebraic property theorems for the predicate   *)
(* logic operators.                                                           *)


open Equal;;
open Bool;;
open EqCong;;


(* HOL variables *)

let p = `p:bool`;;
let q = `q:bool`;;
let r = `r:bool`;;
let x = `x:'a`;;



(* not_true_thm : thm                                                         *)
(*                                                                            *)
(*    |- ~ true <=> false                                                     *)

let not_true_thm = save_thm ("not_true_thm",
  (* |- ~ true <=> false         *)
  deduct_antisym_rule
    (* false |- ~ true             *)
    (contr_rule `~ true` (assume_rule `false`))
    (* ~ true |- false             *)
    (eq_mp_rule
      (* ~ true |- true <=> false    *)
      (eqf_intro_rule (assume_rule `~ true`))
      truth_thm )
);;


(* not_false_thm : thm                                                        *)
(*                                                                            *)
(*    |- ~ false <=> true                                                     *)

let not_false_thm = save_thm ("not_false_thm",
  (* |- ~ false <=> true         *)
  deduct_antisym_rule
    (* |- ~ false            *)
    (not_intro_rule (disch_rule `false` (assume_rule `false`)))
    (* |- true               *)
    truth_thm
);;


(* true_not_eq_false_thm : thm                                                *)
(*                                                                            *)
(*    |- ~ (true <=> false)                                                   *)

let true_not_eq_false_thm = save_thm ("true_not_eq_false_thm",
  eqf_elim_rule
   (deduct_antisym_rule
     (* false |- true <=> false         *)
     (eq_sym_rule (eqt_intro_rule (assume_rule `false`)))
     (* true <=> false |- false         *)
     (eq_mp_rule (assume_rule `true <=> false`) truth_thm) )
);;


(* not_dist_disj_thm : thm                                                    *)
(*                                                                            *)
(*    |- !p q. ~ (p \/ q) <=> ~ p /\ ~ q                                      *)

let not_dist_disj_thm = save_thm ("not_dist_disj_thm",
  let th1 = assume_rule `~ p /\ ~ q` in
  list_gen_rule [p;q]
    (deduct_antisym_rule
      (* ~ p /\ ~ q |- ~ (p \/ q)        *)
      (not_intro_rule
        (disch_rule `p \/ q`
          (* ~ p /\ ~ q, p \/ q |- false   *)
          (disj_cases_rule (assume_rule `p \/ q`)
            (* ~ p /\ ~ q, p |- false        *)
            (undisch_rule (not_elim_rule (conjunct1_rule th1)))
            (* ~ p /\ ~ q, q |- false        *)
            (undisch_rule (not_elim_rule (conjunct2_rule th1))) )))
      (* ~ (p \/ q) |- ~ p /\ ~ q        *)
      (conj_rule
        (* ~ (p \/ q) |- ~ p               *)
        (deduct_contrapos_rule p
          (* p |- p \/ q                      *)
          (disj1_rule (assume_rule p) q) )
        (* ~ (p \/ q) |- ~ q               *)
        (deduct_contrapos_rule q
          (* q |- p \/ q                      *)
          (disj2_rule p (assume_rule q)) )))
);;


(* conj_id_thm                                                                *)
(*                                                                            *)
(*    |- !p. p /\ true <=> p                                                  *)

let conj_id_thm = save_thm ("conj_id_thm",
  gen_rule p
    (deduct_antisym_rule
      (conj_rule (assume_rule p) truth_thm)
      (conjunct1_rule (assume_rule `p /\ true`)) )
);;


(* conj_zero_thm                                                              *)
(*                                                                            *)
(*    |- !p. p /\ false <=> false                                             *)

let conj_zero_thm = save_thm ("conj_zero_thm",
  gen_rule p
    (deduct_antisym_rule
      (contr_rule `p /\ false` (assume_rule false_tm))
      (conjunct2_rule (assume_rule `p /\ false`)) )
);;


(* conj_idem_thm                                                              *)
(*                                                                            *)
(*    |- !p. p /\ p <=> p                                                     *)

let conj_idem_thm = save_thm ("conj_idem_thm",
  gen_rule p
    (deduct_antisym_rule
      (conj_rule (assume_rule p) (assume_rule p))
      (conjunct1_rule (assume_rule `p /\ p`)) )
);;


(* conj_comm_thm                                                              *)
(*                                                                            *)
(*    |- !p q. p /\ q <=> q /\ p                                              *)

let conj_comm_thm = save_thm ("conj_comm_thm",
  let th1 = assume_rule `p /\ q` in
  let th2 = conj_rule (conjunct2_rule th1) (conjunct1_rule th1) in
  list_gen_rule [p;q]
    (deduct_antisym_rule
      (inst_rule [(p,q);(q,p)] th2)       (* q /\ p |- p /\ q      *)
      th2)                                (* p /\ q |- q /\ p      *)
);;


(* conj_assoc_thm                                                             *)
(*                                                                            *)
(*    |- !p q r. p /\ (q /\ r) <=> (p /\ q) /\ r                              *)

let conj_assoc_thm = save_thm ("conj_assoc_thm",
  let th1 = assume_rule `p /\ (q /\ r)` in
  let th2 = assume_rule `(p /\ q) /\ r` in
  list_gen_rule [p;q;r]
    (deduct_antisym_rule
      (* (p /\ q) /\ r |- p /\ (q /\ r)           *)
      (conj_rule
        (conjunct1_rule (conjunct1_rule th2))
        (conj_rule
          (conjunct2_rule (conjunct1_rule th2))
          (conjunct2_rule th2) ))
      (* (p /\ q) /\ r |- (p /\ q) /\ r           *)
      (conj_rule
        (conj_rule
          (conjunct1_rule th1)
          (conjunct1_rule (conjunct2_rule th1)) )
        (conjunct2_rule (conjunct2_rule th1)) ))
);;


(* conj_absorb_disj_thm                                                       *)
(*                                                                            *)
(*    |- !p q. p /\ (p \/ q) <=> p                                            *)

let conj_absorb_disj_thm = save_thm ("conj_absorb_disj_thm",
  let th1 = assume_rule p in
  list_gen_rule [p;q]
    (deduct_antisym_rule
      (conj_rule th1 (disj1_rule th1 q))
      (conjunct1_rule (assume_rule `p /\ (p \/ q)`)) )
);;


(* conj_dist_right_disj_thm                                                   *)
(*                                                                            *)
(*    |- !p q r. p /\ (q \/ r) <=> (p /\ q) \/ (p /\ r)                       *)

let conj_dist_right_disj_thm = save_thm ("conj_dist_right_disj_thm",
  let th1 = assume_rule `(p /\ q) \/ (p /\ r)` in
  let th2 = assume_rule `p /\ (q \/ r)` in
  list_gen_rule [p;q;r]
    (deduct_antisym_rule
      (* (p /\ q) \/ (p /\ r) |- p /\ (q \/ r)  *)
      (conj_rule
        (* (p /\ q) \/ (p /\ r) |- p              *)
        (disj_cases_rule th1
          (conjunct1_rule (assume_rule `p /\ q`))
          (conjunct1_rule (assume_rule `p /\ r`)) )
        (* (p /\ q) \/ (p /\ r) |- q \/ r         *)
        (disj_cases_rule th1
          (disj1_rule (conjunct2_rule (assume_rule `p /\ q`)) r)
          (disj2_rule q (conjunct2_rule (assume_rule `p /\ r`))) ))
      (* p /\ (q \/ r) |- (p /\ q) \/ (p /\ r)  *)
      (disj_cases_rule (conjunct2_rule th2)
        (disj1_rule
          (* p /\ (q \/ r), q |- p /\ q             *)
          (conj_rule (conjunct1_rule th2) (assume_rule q)) `p /\ r`)
        (disj2_rule `p /\ q`
          (* p /\ (q \/ r), r |- p /\ r             *)
          (conj_rule (conjunct1_rule th2) (assume_rule r)) )))
);;


(* conj_dist_left_disj_thm                                                    *)
(*                                                                            *)
(*    |- !p q r. (p \/ q) /\ r <=> (p /\ r) \/ (q /\ r)                       *)

let conj_dist_left_disj_thm = save_thm ("conj_dist_left_disj_thm",
  list_gen_rule [p;q;r]
    (list_eq_trans_rule
       [ list_spec_rule [`p\/q`;r] conj_comm_thm;
         list_spec_rule [r;p;q] conj_dist_right_disj_thm;
         mk_bin_rule `$\/`
           (list_spec_rule [r;p] conj_comm_thm)
           (list_spec_rule [r;q] conj_comm_thm) ])
);;


(* conj_contr_thm                                                             *)
(*                                                                            *)
(*    |- !p. p /\ ~ p <=> false                                               *)

let conj_contr_thm = save_thm ("conj_contr_thm",
  let th1 = assume_rule `p /\ ~p` in
  gen_rule p
    (eqf_intro_rule
      (not_intro_rule
        (disch_rule `p /\ ~p`
          (* p /\ ~p |- false         *)
          (mp_rule
            (not_elim_rule (conjunct2_rule th1))
            (conjunct1_rule th1) ))))
);;


(* disj_id_thm                                                                *)
(*                                                                            *)
(*    |- !p. p \/ false <=> p                                                 *)

let disj_id_thm = save_thm ("disj_id_thm",
  gen_rule p
    (deduct_antisym_rule
      (* p |- p \/ false                   *)
      (disj1_rule (assume_rule p) `false`)
      (* p \/ false |- p                   *)
      (disj_cases_rule (assume_rule `p \/ false`)
        (assume_rule p)
        (contr_rule p (assume_rule `false`)) ))
);;


(* disj_zero_thm                                                              *)
(*                                                                            *)
(*    |- !p. p \/ true <=> true                                               *)

let disj_zero_thm = save_thm ("disj_zero_thm",
  gen_rule p
    (deduct_antisym_rule
      (disj2_rule p truth_thm)
      truth_thm )
);;


(* disj_idem_thm                                                              *)
(*                                                                            *)
(*    |- !p. p \/ p <=> p                                                     *)

let disj_idem_thm = save_thm ("disj_idem_thm",
  let th1 = assume_rule p in
  gen_rule p
    (deduct_antisym_rule
      (disj1_rule (assume_rule p) p)
      (disj_cases_rule (assume_rule `p \/ p`) th1 th1) )
);;


(* disj_comm_thm                                                              *)
(*                                                                            *)
(*    |- !p q. p \/ q <=> q \/ p                                              *)

let disj_comm_thm = save_thm ("disj_comm_thm",
  let th1 = disj_cases_rule                     (* p \/ q |- q \/ p      *)
              (assume_rule `p \/ q`)
              (disj2_rule q (assume_rule p))
              (disj1_rule (assume_rule q) p) in
  let th2 = inst_rule [(p,q);(q,p)] th1 in      (* q \/ p |- p \/ q      *)
  list_gen_rule [p;q]
    (deduct_antisym_rule th2 th1)
);;


(* disj_assoc_thm                                                             *)
(*                                                                            *)
(*    |- !p q r. p \/ (q \/ r) <=> (p \/ q) \/ r                              *)

let disj_assoc_thm = save_thm ("disj_assoc_thm",
  list_gen_rule [p;q;r]
    (deduct_antisym_rule
      (* (p \/ q) \/ r |- p \/ (q \/ r)      *)
      (disj_cases_rule (assume_rule `(p \/ q) \/ r`)
        (* p \/ q |- p \/ (q \/ r)             *)
        (disj_cases_rule (assume_rule `p \/ q`)
          (disj1_rule (assume_rule p) `q \/ r`)
          (disj2_rule p (disj1_rule (assume_rule q) r)))
        (* r |- p \/ (q \/ r)                  *)
        (disj2_rule p (disj2_rule q (assume_rule r))) )
      (* p \/ (q \/ r) |- (p \/ q) \/ r      *)
      (disj_cases_rule (assume_rule `p \/ (q \/ r)`)
        (* p |- (p \/ q) \/ r                    *)
        (disj1_rule (disj1_rule (assume_rule p) q) r)
        (* q \/ r |- (p \/ q) \/ r               *)
        (disj_cases_rule (assume_rule `q \/ r`)
          (disj1_rule (disj2_rule p (assume_rule q)) r)
          (disj2_rule `p \/ q` (assume_rule r)) )))
);;


(* disj_absorb_conj_thm                                                       *)
(*                                                                            *)
(*    |- !p q. p \/ (p /\ q) <=> p                                            *)

let disj_absorb_conj_thm = save_thm ("disj_absorb_conj_thm",
  list_gen_rule [p;q]
    (deduct_antisym_rule
      (* p |- p \/ (p /\ q)           *)
      (disj1_rule (assume_rule p) `p /\ q`)
      (* p \/ (p /\ q) |- p           *)
      (disj_cases_rule (assume_rule `p \/ (p /\ q)`)
         (assume_rule p)
         (conjunct1_rule (assume_rule `p /\ q`)) ))
);;


(* disj_dist_right_conj_thm                                                   *)
(*                                                                            *)
(*    |- !p q r. p \/ (q /\ r) <=> (p \/ q) /\ (p \/ r)                       *)

let disj_dist_right_conj_thm = save_thm ("disj_dist_right_conj_thm",
  let th1 = assume_rule `(p \/ q) /\ (p \/ r)` in
  list_gen_rule [p;q;r]
    (deduct_antisym_rule
      (* (p \/ q) /\ (p \/ r) |- p \/ (q /\ r)    *)
      (disj_cases_rule (conjunct2_rule th1)
        (* p |- p \/ (q /\ r)                       *)
        (disj1_rule (assume_rule p) `q /\ r`)
        (* (p \/ q) /\ (p \/ r), r |- p \/ (q /\ r) *)
        (disj_cases_rule (conjunct1_rule th1)
          (* p |- p \/ (q /\ r)                       *)
          (disj1_rule (assume_rule p) `q /\ r`)
          (* q, r |- p \/ (q /\ r)                    *)
          (disj2_rule p (conj_rule (assume_rule q) (assume_rule r))) ))
      (* p \/ (q /\ r) |- (p \/ q) /\ (p \/ r)    *)
      (disj_cases_rule (assume_rule `p \/ (q /\ r)`)
        (* p |- (p \/ q) /\ (p \/ r)                *)
        (conj_rule
          (disj1_rule (assume_rule p) q)
          (disj1_rule (assume_rule p) r) )
        (* q /\ r |- (p \/ q) /\ (p \/ r)           *)
        (conj_rule
          (disj2_rule p (conjunct1_rule (assume_rule `q /\ r`)))
          (disj2_rule p (conjunct2_rule (assume_rule `q /\ r`))) )))
);;


(* disj_dist_left_conj_thm                                                    *)
(*                                                                            *)
(*    |- !p q r. (p /\ q) \/ r <=> (p \/ r) /\ (q \/ r)                       *)

let disj_dist_left_conj_thm = save_thm ("disj_dist_left_conj_thm",
  list_gen_rule [p;q;r]
    (list_eq_trans_rule
       [ list_spec_rule [`p/\q`;r] disj_comm_thm;
         list_spec_rule [r;p;q] disj_dist_right_conj_thm;
         mk_bin_rule `$/\`
           (list_spec_rule [r;p] disj_comm_thm)
           (list_spec_rule [r;q] disj_comm_thm) ])
);;


(* imp_right_zero_thm                                                         *)
(*                                                                            *)
(*    |- !p. p ==> true                                                       *)

let imp_right_zero_thm = save_thm ("imp_right_zero_thm",
  gen_rule p (disch_rule p truth_thm)
);;


(* imp_left_id_thm                                                            *)
(*                                                                            *)
(*    |- !p. (true ==> p) <=> p                                               *)

let imp_left_id_thm = save_thm ("imp_left_id_thm",
  gen_rule p
    (deduct_antisym_rule
      (disch_rule `true` (assume_rule p))
      (mp_rule (assume_rule `true ==> p`) truth_thm) )
);;


(* imp_left_zero_thm                                                          *)
(*                                                                            *)
(*    |- !p. false ==> p                                                      *)

let imp_left_zero_thm = save_thm ("imp_left_zero_thm",
  gen_rule p (disch_rule `false` (contr_rule p (assume_rule `false`)))
);;


(* imp_refl_thm                                                               *)
(*                                                                            *)
(*    |- !p. p ==> p                                                          *)

let imp_refl_thm = save_thm ("imp_refl_thm",
  gen_rule p (disch_rule p (assume_rule p))
);;


(* imp_dist_left_disj_thm                                                     *)
(*                                                                            *)
(*    |- !p q r. (p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)                    *)

let imp_dist_left_disj_thm = save_thm ("imp_dist_left_disj_thm",
  let th1 = assume_rule `(p ==> r) /\ (q ==> r)` in
  let th2 = assume_rule `p \/ q ==> r` in
  list_gen_rule [p;q;r]
    (deduct_antisym_rule
      (* (p ==> r) /\ (q ==> r) |- p \/ q ==> r      *)
      (disch_rule `p \/ q`
        (disj_cases_rule (assume_rule `p \/ q`)
           (* (p ==> r) /\ (q ==> r), p |- r             *)
           (mp_rule (conjunct1_rule th1) (assume_rule p))
           (* (p ==> r) /\ (q ==> r), q |- r             *)
           (mp_rule (conjunct2_rule th1) (assume_rule q)) ))
      (* p \/ q ==> r |- (p ==> r) /\ (q ==> r)      *)
      (conj_rule
        (imp_trans_rule
          (disch_rule p (disj1_rule (assume_rule p) q))
          th2 )
        (imp_trans_rule
          (disch_rule q (disj2_rule p (assume_rule q)))
          th2 )))
);;


(* imp_dist_right_conj_thm                                                    *)
(*                                                                            *)
(*    |- !p q r. (p ==> q /\ r) <=> (p ==> q) /\ (p ==> r)                    *)

let imp_dist_right_conj_thm = save_thm ("imp_dist_right_conj_thm",
  let th1 = assume_rule `(p ==> q) /\ (p ==> r)` in
  let th2 = assume_rule `p ==> q /\ r` in
  list_gen_rule [p;q;r]
    (deduct_antisym_rule
      (* (p ==> q) /\ (p ==> r) |- (p ==> q /\ r)       *)
      (disch_rule p
        (conj_rule
          (undisch_rule (conjunct1_rule th1))
          (undisch_rule (conjunct2_rule th1)) ))
      (* (p ==> q /\ r) |- (p ==> q) /\ (p ==> r)       *)
      (conj_rule
        (disch_rule p (conjunct1_rule (undisch_rule th2)))
        (disch_rule p (conjunct2_rule (undisch_rule th2))) ))
);;


(* imp_imp_thm                                                                *)
(*                                                                            *)
(*    |- !p q r. (p ==> q ==> r) <=> (p /\ q ==> r)                           *)

let imp_imp_thm = save_thm ("imp_imp_thm",
  let th1 = assume_rule `p /\ q` in
  list_gen_rule [p;q;r]
    (deduct_antisym_rule
      (* p /\ q ==> r |- p ==> q ==> r                *)
      (disch_rule p (disch_rule q
        (mp_rule
          (assume_rule `p /\ q ==> r`)
          (conj_rule (assume_rule p) (assume_rule q)) )))
      (* p ==> q ==> r |- p /\ q ==> r                *)
      (disch_rule `p /\ q`
        (mp_rule
          (mp_rule
            (assume_rule `p ==> q ==> r`)
            (conjunct1_rule th1) )
          (conjunct2_rule th1) )))
);;


(* forall_dist_conj_thm                                                       *)
(*                                                                            *)
(*    |- !P Q. (!x. P x /\ Q x) <=> (!x. P x) /\ (!x. Q x)                    *)

let forall_dist_conj_thm = save_thm ("forall_dist_conj_thm",
  let th1 = assume_rule `(!(x:'a). P x) /\ (!(x:'a). Q x)` in
  let th2 = assume_rule `!(x:'a). P x /\ Q x` in
  list_gen_rule [`P:'a->bool`;`Q:'a->bool`]
    (deduct_antisym_rule
      (* (!x. P x) /\ (!x. Q x) |- !x. P x /\ Q x     *)
      (gen_rule x
        (conj_rule
          (spec_rule x (conjunct1_rule th1))
          (spec_rule x (conjunct2_rule th1)) ))
      (* !x. P x /\ Q x |- (!x. P x) /\ (!x. Q x)     *)
      (conj_rule
        (gen_rule x (conjunct1_rule (spec_rule x th2)))
        (gen_rule x (conjunct2_rule (spec_rule x th2))) ))
);;


(* forall_one_point_thm                                                       *)
(*                                                                            *)
(*    |- !P a. (!x. x = a ==> P x) <=> P a                                    *)

let forall_one_point_thm = save_thm ("forall_one_point_thm",
  let a = `a:'a`  and x = `x:'a`  and p = `P:'a->bool` in
  list_gen_rule [p;a]
   (deduct_antisym_rule
     (gen_rule x
       (disch_rule `(x:'a) = a`
         (eq_mp_rule
           (eq_sym_rule (mk_comb2_rule p (assume_rule `(x:'a) = a`)))
           (assume_rule `(P:'a->bool) a`) )))
     (mp_rule
       (spec_rule a (assume_rule `!(x:'a). x = a ==> P x`))
       (eq_refl_conv a) ))
);;


(* forall_null_thm                                                            *)
(*                                                                            *)
(*    |- !t. (!(x:'a). t) <=> t                                               *)

let forall_null_thm = save_thm ("forall_null_thm",
  let t = `t:bool` and x = `x:'a` in
  gen_rule t
    (deduct_antisym_rule
      (gen_rule x (assume_rule t))
      (spec_rule x (assume_rule `!(x:'a). t`)) )
);;


end;;
