(* ========================================================================== *)
(* NATURAL NUMBER RELATIONS (HOL Zero)                                        *)
(* - Theory defining natural number relations; derived properties             *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2010-2015                            *)
(* ========================================================================== *)


module NatRel : NatRel_sig = struct


(* This module defines the classic natural number arithmetic relations and    *)
(* derives various basic properties about them.                               *)


open Def2;;

open Equal;;
open EqCong;;
open Bool;;
open BoolAlg;;
open BoolClass;;

open Nat;;
open NatNumrl;;
open NatArith;;


(* HOL variables *)

let l = `l:nat`;;
let m = `m:nat`;;
let n = `n:nat`;;



(* ** THEOREMS ABOUT EQUALITY ** *)


(* add_eq_cancel_thm                                                          *)
(*                                                                            *)
(*    |- !l m n. l + n = m + n <=> l = m                                      *)

let add_eq_cancel_thm = save_thm ("add_eq_cancel_thm",
  list_gen_rule [l;m]
    (mp_rule
      (bspec_rule `\n. l + n = m + n <=> l = m` nat_induction_thm)
      (conj_rule
        (* |- l + 0 = m + 0 <=> l = m                          *)
        (mk_eq_rule (spec_rule l add_id_thm)
                    (spec_rule m add_id_thm) )
        (* |- !n. (l + n = m + n <=> l = m)                    *)
        (*        ==> (l + SUC n = m + SUC n <=> l = m)        *)
        (gen_rule n
          (disch_rule `l + n = m + n <=> l = m`
            (list_eq_trans_rule
               [ (* |- l + SUC n = m + SUC n <=> SUC (l + n) = SUC (m + n)  *)
                 mk_eq_rule
                   (list_spec_rule [l;n] add_dist_right_suc_thm)
                   (list_spec_rule [m;n] add_dist_right_suc_thm);
                 (* |- ...                   <=> l + n = m + n              *)
                 list_spec_rule [`l+n`;`m+n`] suc_injective_thm;
                 (* l + n = m + n <=> l = m                                 *)
                 (*      |- ...              <=> l = m                      *)
                 assume_rule `l + n = m + n <=> l = m` ])))))
);;


(* add_eq_zero_thm                                                            *)
(*                                                                            *)
(*    |- !m n. m + n = 0 <=> m = 0 /\ n = 0                                   *)

let add_eq_zero_thm = save_thm ("add_eq_zero_thm",
  gen_rule m
    (mp_rule
      (bspec_rule `\n. m + n = 0 <=> m = 0 /\ n = 0` nat_induction_thm)
      (conj_rule
        (* |- m + 0 = 0 <=> m = 0 /\ 0 = 0                     *)
        (list_eq_trans_rule
           [ (* |- m + 0 = 0 <=> m = 0                           *)
             mk_eq1_rule (spec_rule m add_id_thm) `0`;
             (* |- ...       <=> m = 0 /\ 0 = 0                  *)
             eq_sym_rule (spec_rule `m=0` conj_id_thm);
             eq_sym_rule
               (mk_conj2_rule `m=0` (eqt_intro_rule (eq_refl_conv `0`))) ])
        (* |- !n. (m + n = 0 <=> m = 0 /\ n = 0)               *)
        (*        ==> (m + SUC n = 0 <=> m = 0 /\ SUC n = 0)   *)
        (gen_rule n
          (disch_rule `m + n = 0 <=> m = 0 /\ n = 0`
            (* |- m + SUC n = 0 <=> m = 0 /\ SUC n = 0           *)
            (list_eq_trans_rule
               [ (* |- m + SUC n = 0 <=> SUC (m + n) = 0           *)
                 mk_eq1_rule (list_spec_rule [m;n] add_dist_right_suc_thm) `0`;
                 (* |- ...           <=> false                     *)
                 eqf_intro_rule (spec_rule `m+n` suc_not_zero_thm);
                 (* |- ...           <=> m = 0 /\ false            *)
                 eq_sym_rule (spec_rule `m=0` conj_zero_thm);
                 (* |- ...           <=> m = 0 /\ SUC n = 0        *)
                 eq_sym_rule
                   (mk_conj2_rule `m=0`
                     (eqf_intro_rule (spec_rule n suc_not_zero_thm))) ] )))))
);;


(* mult_eq_zero_thm                                                           *)
(*                                                                            *)
(*    |- !m n. m * n = 0 <=> m = 0 \/ n = 0                                   *)

let mult_eq_zero_thm = save_thm ("mult_eq_zero_thm",
  gen_rule m
    (mp_rule
      (bspec_rule `\n. m * n = 0 <=> m = 0 \/ n = 0` nat_induction_thm)
      (conj_rule
        (* |- m * 0 = 0 <=> m = 0 \/ 0 = 0              *)
        (eq_trans_rule
          (* |- m * 0 = 0 <=> true                        *)
          (eqt_intro_rule (spec_rule m mult_zero_thm))
          (* |- ...       <=> m = 0 \/ 0 = 0              *)
          (eq_sym_rule
            (eqt_intro_rule (disj2_rule `m = 0` (eq_refl_conv `0`))) ))
        (* |- !n. (m * n = 0 <=> m = 0 \/ n = 0)                *)
        (*        ==> (m * SUC n = 0 <=> m = 0 \/ SUC n = 0)    *)
        (gen_rule n
          (disch_rule `m * n = 0 <=> m = 0 \/ n = 0`
            (list_eq_trans_rule
               [ (* |- m * SUC n = 0 <=> m + m * n = 0              *)
                 mk_eq1_rule
                   (list_spec_rule [m;n] mult_dist_right_suc_thm) `0`;
                 (* |- ...           <=> m = 0 /\ m * n = 0         *)
                 list_spec_rule [m;`m*n`] add_eq_zero_thm;
                 (* m * n = 0 <=> m = 0 \/ n = 0                    *)
                 (*    |- ...        <=> m = 0 /\ (m = 0 \/ n = 0)  *)
                 mk_conj2_rule `m=0`
                   (assume_rule `m * n = 0 <=> m = 0 \/ n = 0`);
                 (* |- ...           <=> m = 0                      *)
                 list_spec_rule [`m=0`;`n=0`] conj_absorb_disj_thm;
                 (* |- ...           <=> m = 0 \/ SUC n = 0         *)
                 eq_sym_rule (spec_rule `m=0` disj_id_thm);
                 eq_sym_rule
                   (mk_disj2_rule `m=0`
                     (eqf_intro_rule (spec_rule n suc_not_zero_thm)) ) ])))))
);;


(* mult_eq_cancel_thm                                                         *)
(*                                                                            *)
(*    |- !l m n. ~ (l = 0) ==> l * m = l * n <=> m = n                        *)

let mult_eq_cancel_thm = save_thm ("mult_eq_cancel_thm",
  list_gen_rule [l;m;n] (disch_rule `~(l=0)` (list_spec_rule [m;n]
    (* ~ (l = 0) |- !m n. l * m = l * n <=> m = n      *)
    (mp_rule
      (bspec_rule `\m. !n. l * m = l * n <=> m = n` nat_induction_thm)
      (conj_rule
        (* |- ~ (l = 0) ==> (!n. l * 0 = l * n <=> 0 = n)           *)
        (gen_rule n
          (list_eq_trans_rule
             [ (* |- l * 0 = l * n <=> 0 = l * n               *)
               mk_eq1_rule (spec_rule l mult_zero_thm) `l*n`;
               (* |- ...           <=> l = 0 \/ n = 0          *)
               eq_sym_conv `0 = l * n`;
               list_spec_rule [l;n] mult_eq_zero_thm;
               (* ~ (l = 0) |- ... <=> n = 0                   *)
               mk_disj1_rule (eqf_intro_rule (assume_rule `~(l=0)`)) `n=0`;
               list_spec_rule [`false`;`n=0`] disj_comm_thm;
               spec_rule `n=0` disj_id_thm;
               eq_sym_conv `n=0` ]))
        (* ~ (l = 0) |- !m. (!n. l * m = l * n <=> m = n)               *)
        (*                  ==> (!n. l * m = l * SUC n <=> m = SUC n)   *)
        (gen_rule m
          (disch_rule `!n. l * m = l * n <=> m = n`
            (mp_rule
              (bspec_rule `\n. l * SUC m = l * n <=> SUC m = n`
                          nat_induction_thm)
              (conj_rule
                (* ~ (l = 0) |- l * SUC m = l * 0 <=> SUC m = 0             *)
                (list_eq_trans_rule
                   [ (* |- l * SUC m = l * 0 <=> l * SUC m = 0              *)
                     mk_eq2_rule `l * SUC m` (spec_rule l mult_zero_thm);
                     (* |- ...               <=> l = 0 \/ SUC m = 0         *)
                     list_spec_rule [l;`SUC m`] mult_eq_zero_thm;
                     (* ~ (l = 0) |- ...     <=> SUC m = 0                  *)
                     list_eq_trans_rule
                       [ mk_disj1_rule
                          (eqf_intro_rule (assume_rule `~(l=0)`)) `SUC m = 0`;
                         list_spec_rule [`false`;`SUC m = 0`] disj_comm_thm;
                         spec_rule `SUC m = 0` disj_id_thm ] ])
                (* !n. l * m = l * n <=> m = n                            *)
                (*   |- !n. (l * SUC m = l * n <=> SUC m = n)             *)
                (*          ==> (l * SUC m = l * SUC n <=> SUC m = SUC n) *)
                (gen_rule n (disch_rule `l * SUC m = l * n <=> SUC m = n`
                  (list_eq_trans_rule
                     [ (* |- l * SUC m = l * SUC n <=> l * m + l = l * n + l  *)
                       mk_eq_rule
                         (eq_trans_rule
                           (list_spec_rule [l;m] mult_dist_right_suc_thm)
                           (list_spec_rule [l;`l*m`] add_comm_thm) )
                         (eq_trans_rule
                           (list_spec_rule [l;n] mult_dist_right_suc_thm)
                           (list_spec_rule [l;`l*n`] add_comm_thm) );
                       (* |- ...                   <=> l * m = l * n          *)
                       list_spec_rule [`l*m`;`l*n`;l] add_eq_cancel_thm;
                       (* !n. l * m = l * n <=> m = n                         *)
                       (*      |-...               <=> m = n                  *)
                       spec_rule n (assume_rule `!n. l * m = l * n <=> m = n`);
                       (* |- ...                   <=> SUC m = SUC n          *)
                       eq_sym_rule
                         (list_spec_rule [m;n] suc_injective_thm) ] )))
                 ))))))))
);;



(* ** LESS THAN ** *)


(* Definition *)

set_fixity ("<", Infix (40,NonAssoc));;

let lt_def =
  new_recursive_fun_definition nat_recursion_thm
   `(!m. m < 0 <=> false) /\
    (!m n. m < SUC n <=> m = n \/ m < n)`;;

let lt_fn = `$<`;;


(* Syntax functions *)

let dest_lt = dest_cbin "<";;

let mk_lt (tm1,tm2) = mk_bin (lt_fn,tm1,tm2);;

let is_lt = can dest_lt;;


(* not_lt_zero_thm                                                            *)
(*                                                                            *)
(*    |- !n. ~ (n < 0)                                                        *)

let not_lt_zero_thm = save_thm ("not_lt_zero_thm",
  gen_rule n (eqf_elim_rule (spec_rule n (conjunct1_rule lt_def)))
);;


(* lt_suc_cases_thm                                                           *)
(*                                                                            *)
(*    |- !m n. m < SUC n <=> m = n \/ m < n                                   *)

let lt_suc_cases_thm = save_thm ("lt_suc_cases_thm",
  conjunct2_rule lt_def
);;


(* lt_suc_thm                                                                 *)
(*                                                                            *)
(*    |- !n. n < SUC n                                                        *)

let lt_suc_thm = save_thm ("lt_suc_thm",
  gen_rule n
    (eq_mp_rule
      (eq_sym_rule (list_spec_rule [n;n] lt_suc_cases_thm))
      (disj1_rule (eq_refl_conv n) `n < n`) )
);;


(* zero_lt_suc_thm                                                            *)
(*                                                                            *)
(*    |- !n. 0 < SUC n                                                        *)

let zero_lt_suc_thm = save_thm ("zero_lt_suc_thm",
  mp_rule
    (bspec_rule `\n. 0 < SUC n` nat_induction_thm)
    (conj_rule
      (* |- 0 < SUC 0                            *)
      (eq_mp_rule
        (* |- 0 = 0 \/ 0 < 0 <=> 0 < SUC 0         *)
        (eq_sym_rule (list_spec_rule [`0`;`0`] lt_suc_cases_thm))
        (* |- 0 = 0 \/ 0 < 0                       *)
        (disj1_rule (eq_refl_conv `0`) `0<0`) )
      (* |- !n. 0 < SUC n ==> 0 < SUC (SUC n)    *)
      (gen_rule n
        (disch_rule `0 < SUC n`
          (eq_mp_rule
            (* |- 0 = SUC n \/ 0 < SUC n <=> 0 < SUC (SUC n)     *)
            (eq_sym_rule (list_spec_rule [`0`;`SUC n`] lt_suc_cases_thm))
            (* 0 < SUC n |- 0 = SUC n \/ 0 < SUC n               *)
            (disj2_rule `0 = SUC n` (assume_rule `0 < SUC n`)) ))))
);;


(* lt_zero_cases_thm                                                          *)
(*                                                                            *)
(*    |- !n. n = 0 \/ 0 < n                                                   *)

let lt_zero_cases_thm = save_thm ("lt_zero_cases_thm",
  gen_rule n
    (eq_mp_rule
      (* |- 0 = n \/ 0 < n <=> n = 0 \/ 0 < n   *)
      (mk_disj1_rule (eq_sym_conv `0=n`) `0<n`)
      (* |- 0 = n \/ 0 < n                      *)
      (eq_mp_rule
        (list_spec_rule [`0`;n] lt_suc_cases_thm)
        (spec_rule n zero_lt_suc_thm) ))
);;


(* suc_lt_cancel_thm                                                          *)
(*                                                                            *)
(*    |- !m n. SUC m < SUC n <=> m < n                                        *)

let suc_lt_cancel_thm = save_thm ("suc_lt_cancel_thm",
  gen_rule m
    (mp_rule
      (bspec_rule `\n. SUC m < SUC n <=> m < n` nat_induction_thm)
      (conj_rule
        (* |- SUC m < SUC 0 <=> m < 0                 *)
        (list_eq_trans_rule
           [ (* |- SUC m < SUC 0 <=> SUC m = 0 \/ SUC m < 0   *)
             list_spec_rule [`SUC m`;`0`] lt_suc_cases_thm;
             (* |- ...           <=> false \/ false           *)
             mk_disj_rule (eqf_intro_rule (spec_rule m suc_not_zero_thm))
                          (eqf_intro_rule (spec_rule `SUC m` not_lt_zero_thm));
             (* |- ...           <=> false                    *)
             spec_rule `false` disj_id_thm;
             (* |- ...           <=> m < 0                    *)
             eq_sym_rule (eqf_intro_rule (spec_rule m not_lt_zero_thm)) ])
        (* |- !n. (SUC m < SUC n <=> m < n)                 *)
        (*        ==> (SUC m < SUC (SUC n) <=> m < SUC n)   *)
        (gen_rule n
          (disch_rule `SUC m < SUC n <=> m < n`
            (list_eq_trans_rule
               [ (* |- SUC m < SUC (SUC n) <=> SUC m = SUC n \/ SUC m < SUC n *)
                 list_spec_rule [`SUC m`;`SUC n`] lt_suc_cases_thm;
                 (* |- ...                 <=> m = n \/ m < n                 *)
                 mk_disj_rule (list_spec_rule [m;n] suc_injective_thm)
                              (assume_rule `SUC m < SUC n <=> m < n`);
                 (* |- ...                 <=> m < SUC n                      *)
                 eq_sym_rule (list_spec_rule [m;n] lt_suc_cases_thm) ])))))
);;


(* lt_irrefl_thm                                                              *)
(*                                                                            *)
(*    |- !n. ~ (n < n)                                                        *)

let lt_irrefl_thm = save_thm ("lt_irrefl_thm",
  mp_rule
    (bspec_rule `\n. ~ (n < n)` nat_induction_thm)
    (conj_rule
      (* |- ~ (0 < 0)                             *)
      (spec_rule `0` not_lt_zero_thm)
      (* |- !n. ~ (n < n) ==> ~ (SUC n < SUC n)   *)
      (gen_rule n
        (eq_imp_rule2
          (mk_not_rule
            (* |- SUC n < SUC n <=> n < n           *)
            (list_spec_rule [n;n] suc_lt_cancel_thm) ))))
);;


(* lt_trans_thm                                                               *)
(*                                                                            *)
(*    |- !l m n. l < m /\ m < n ==> l < n                                     *)

let lt_trans_thm = save_thm ("lt_trans_thm",
  let th1 = assume_rule `l < m /\ m < SUC n` in
  list_gen_rule [l;m]
    (mp_rule
      (bspec_rule `\n. l < m /\ m < n ==> l < n` nat_induction_thm)
      (conj_rule
        (* |- l < m /\ m < 0 ==> l < 0                    *)
        (disch_rule `l < m /\ m < 0`
          (contr_rule `l<0`
            (mp_rule
              (not_elim_rule (spec_rule m not_lt_zero_thm))
              (conjunct2_rule (assume_rule `l < m /\ m < 0`)) )))
        (* |- !n. (l < m /\ m < n ==> l < n)              *)
        (*        ==> (l < m /\ m < SUC n ==> l < SUC n)  *)
        (gen_rule n
          (disch_rule `l < m /\ m < n ==> l < n`
            (disch_rule `l < m /\ m < SUC n`
              (eq_mp_rule
                (* |- l = n \/ l < n <=> l < SUC n                *)
                (eq_sym_rule (list_spec_rule [l;n] lt_suc_cases_thm))
                (disj2_rule `(l:nat)=n`
                  (* l < m /\ m < n ==> l < n, l < m /\ m < SUC n   *)
                  (*    |- l < n                                    *)
                  (disj_cases_rule (* l < m /\ m < SUC n |- m = n \/ m < n    *)
                                   (eq_mp_rule
                                     (list_spec_rule [m;n] lt_suc_cases_thm)
                                     (conjunct2_rule th1) )
                    (* l < m /\ m < SUC n, m = n |- l < n             *)
                    (eq_mp_rule
                      (mk_bin2_rule `$<` l (assume_rule `(m:nat)=n`))
                      (conjunct1_rule th1) )
                    (* l < m /\ m < n ==> l < n, l < m /\ m < SUC n,  *)
                    (*    m < n |- l < n                              *)
                    (mp_rule
                      (assume_rule `l < m /\ m < n ==> l < n`)
                      (conj_rule (conjunct1_rule th1) (assume_rule `m<n`)) ))))
                         )))))
);;


(* lt_asym_thm                                                                *)
(*                                                                            *)
(*    |- !m n. ~ (m < n /\ n < m)                                             *)

let lt_asym_thm = save_thm ("lt_asym_thm",
  list_gen_rule [m;n]
    (not_intro_rule
      (imp_trans_rule
        (* |- m < n /\ n < m ==> m < m       *)
        (list_spec_rule [m;n;m] lt_trans_thm)
        (* |- m < m ==> false                *)
        (not_elim_rule (spec_rule m lt_irrefl_thm)) ))
);;


(* zero_lt_thm                                                                *)
(*                                                                            *)
(*    |- !n. 0 < n <=> ~ (n = 0)                                              *)

let zero_lt_thm = save_thm ("zero_lt_thm",
  mp_rule
    (bspec_rule `\n. 0 < n <=> ~ (n = 0)` nat_induction_thm)
    (conj_rule
      (* |- 0 < 0 <=> ~ (0 = 0)                                          *)
      (eq_trans_rule
        (eq_sym_rule (spec_rule `0<0` not_dneg_thm))
        (deduct_antisym_rule
          (deduct_contrapos_rule `~(0<0)` (eq_refl_conv `0`) )
          (deduct_contrapos_rule `0=0` (spec_rule `0` lt_irrefl_thm) )))
      (* |- !n. (0 < n <=> ~ (n = 0)) ==> (0 < SUC n <=> ~ (SUC n = 0))  *)
      (gen_rule n
        (disch_rule `0 < n <=> ~ (n = 0)`
          (deduct_antisym_rule
            (spec_rule n zero_lt_suc_thm)
            (spec_rule n suc_not_zero_thm) ))))
);;


(* not_lt_cases_thm                                                           *)
(*                                                                            *)
(*    |- !m n. ~ (m < n) <=> n = m \/ n < m                                   *)

let not_lt_cases_thm = save_thm ("not_lt_cases_thm",
  list_gen_rule [m;n] (list_spec_rule [m;n]
    (mp_rule
      (bspec_rule `\m. !n. ~ (m < n) <=> n = m \/ n < m` nat_induction_thm)
      (conj_rule
        (* |- !n. ~ (0 < n) <=> n = 0 \/ n < 0                      *)
        (gen_rule n
          (list_eq_trans_rule
             [ (* |- ~ (0 < n) <=> ~ ~ (n = 0)           *)
               mk_not_rule (spec_rule n zero_lt_thm);
               (* |- ...       <=> n = 0                 *)
               spec_rule `n=0` not_dneg_thm;
               (* |- ...       <=> n = 0 \/ n < 0        *)
               eq_sym_rule (spec_rule `n=0` disj_id_thm);
               eq_sym_rule
                 (mk_disj2_rule `n=0`
                   (eqf_intro_rule (spec_rule n not_lt_zero_thm))) ]))
        (* !m. (!n. ~ (m < n) <=> n = m \/ n < m)                   *)
        (*     ==> (!n. ~ (SUC m < n) <=> n = SUC m \/ n < SUC m)   *)
        (gen_rule m
          (disch_rule `!n. ~ (m < n) <=> n = m \/ n < m`
            (mp_rule
              (bspec_rule `\n. ~ (SUC m < n) <=> n = SUC m \/ n < SUC m`
                          nat_induction_thm)
              (conj_rule
                (* |- ~ (SUC m < 0) <=> 0 = SUC m \/ 0 < SUC m            *)
                (deduct_antisym_rule
                  (* |- ~ (SUC m < 0)                                       *)
                  (spec_rule `SUC m` not_lt_zero_thm)
                  (* |- 0 = SUC m \/ 0 < SUC m                              *)
                  (eq_mp_rule
                    (list_spec_rule [`0`;`SUC m`] lt_suc_cases_thm)
                    (spec_rule `SUC m` zero_lt_suc_thm) ))
                (* |- !n. (~ (SUC m < n) <=> n = SUC m \/ n < SUC m)      *)
                (*        ==> (~ (SUC m < SUC n) <=>                      *)
                (*                      SUC n = SUC m \/ SUC n < SUC m)   *)
                (gen_rule n
                  (disch_rule `~ (SUC m < n) <=> n = SUC m \/ n < SUC m`
                    (eq_mp_rule
                      (* |- (~ (m < n) <=> n = m \/ n < m)                    *)
                      (*    <=> (~ (SUC m < SUC n) <=>                        *)
                      (*                    SUC n = SUC m \/ SUC n < SUC m)   *)
                      (eq_sym_rule
                        (mk_eq_rule
                          (mk_not_rule (list_spec_rule [m;n] suc_lt_cancel_thm))
                          (mk_disj_rule
                            (* |- SUC n = SUC m <=> n = m            *)
                            (list_spec_rule [n;m] suc_injective_thm)
                            (* |- SUC n < SUC m <=> n < m            *)
                            (list_spec_rule [n;m] suc_lt_cancel_thm) )))
                      (spec_rule n
                        (assume_rule `!n. ~ (m < n) <=> n = m \/ n < m`) ))))
                   )))))))
);;


(* add_lt_cancel_thm                                                          *)
(*                                                                            *)
(*    |- !l m n. l + n < m + n <=> l < m                                      *)

let add_lt_cancel_thm = save_thm ("add_lt_cancel_thm",
  list_gen_rule [l;m]
    (mp_rule
      (bspec_rule `\n. l + n < m + n <=> l < m` nat_induction_thm)
      (conj_rule
        (* |- l + 0 < m + 0 <=> l < m                     *)
        (mk_bin_rule `$<` (spec_rule l add_id_thm) (spec_rule m add_id_thm))
        (* |- !n. (l + n < m + n <=> l < m)               *)
        (*        ==> (l + SUC n < m + SUC n <=> l < m)   *)
        (gen_rule n
          (disch_rule `l + n < m + n <=> l < m`
            (list_eq_trans_rule
               [ (* |- l + SUC n < m + SUC n <=> SUC (l + n) < SUC (m + n)   *)
                 mk_bin_rule `$<`
                   (list_spec_rule [l;n] add_dist_right_suc_thm)
                   (list_spec_rule [m;n] add_dist_right_suc_thm);
                 (* |- ...                   <=> l + n < m + n               *)
                 list_spec_rule [`l+n`;`m+n`] suc_lt_cancel_thm;
                 (* l + n < m + n <=> l < m                                  *)
                 (*       |- ...             <=> l < m                       *)
                 assume_rule `l + n < m + n <=> l < m` ] )))))
);;


(* mult_lt_cancel_thm                                                         *)
(*                                                                            *)
(*    |- !l m n. ~ (l = 0) ==> l * m < l * n <=> m < n                        *)

let mult_lt_cancel_thm = save_thm ("mult_lt_cancel_thm",
  list_gen_rule [l;m;n] (disch_rule `~(l=0)` (list_spec_rule [m;n]
    (* ~ (l = 0) |- !m n. l * m < l * n <=> m < n      *)
    (mp_rule
      (bspec_rule `\m. !n. l * m < l * n <=> m < n` nat_induction_thm)
      (conj_rule
        (* |- ~ (l = 0) ==> (!n. l * 0 < l * n <=> 0 < n)           *)
        (gen_rule n
          (list_eq_trans_rule
             [ (* |- l * 0 < l * n <=> 0 < l * n               *)
               mk_bin1_rule `$<` (spec_rule l mult_zero_thm) `l*n`;
               (* |- ...           <=> ~ (l * n = 0)           *)
               spec_rule `l*n` zero_lt_thm;
               (* |- ...           <=> ~ (l = 0 \/ n = 0)      *)
               mk_not_rule (list_spec_rule [l;n] mult_eq_zero_thm);
               (* |- ...           <=> ~ (l = 0) /\ ~ (n = 0)  *)
               list_spec_rule [`l=0`;`n=0`] not_dist_disj_thm;
               (* ~ (l = 0) |- ... <=> ~ (n = 0)               *)
               deduct_antisym_rule
                 (conj_rule (assume_rule `~(l=0)`) (assume_rule `~(n=0)`))
                 (conjunct2_rule (assume_rule `~ (l = 0) /\ ~ (n = 0)`));
               (* |- ...           <=> 0 < n                   *)
               eq_sym_rule (spec_rule n zero_lt_thm) ]))
        (* ~ (l = 0) |- !m. (!n. l * m < l * n <=> m < n)               *)
        (*                  ==> (!n. l * m < l * SUC n <=> m < SUC n)   *)
        (gen_rule m
          (disch_rule `!n. l * m < l * n <=> m < n`
            (mp_rule
              (bspec_rule `\n. l * SUC m < l * n <=> SUC m < n`
                          nat_induction_thm)
              (conj_rule
                (* |- l * SUC m < l * 0 <=> SUC m < 0                     *)
                (list_eq_trans_rule
                   [ (* |- l * SUC m < l * 0 <=> l * SUC m < 0              *)
                     mk_bin2_rule `$<` `l * SUC m` (spec_rule l mult_zero_thm);
                     (* |- ...               <=> false                      *)
                     eqf_intro_rule (spec_rule `l * SUC m` not_lt_zero_thm);
                     (* |- ...               <=> SUC m < 0                  *)
                     eq_sym_rule
                       (eqf_intro_rule (spec_rule `SUC m` not_lt_zero_thm)) ])
                (* !n. l * m < l * n <=> m < n                            *)
                (*   |- !n. (l * SUC m < l * n <=> SUC m < n)             *)
                (*          ==> (l * SUC m < l * SUC n <=> SUC m < SUC n) *)
                (gen_rule n (disch_rule `l * SUC m < l * n <=> SUC m < n`
                  (list_eq_trans_rule
                     [ (* |- l * SUC m < l * SUC n <=> l * m + l < l * n + l  *)
                       mk_bin_rule `$<`
                         (eq_trans_rule
                           (list_spec_rule [l;m] mult_dist_right_suc_thm)
                           (list_spec_rule [l;`l*m`] add_comm_thm) )
                         (eq_trans_rule
                           (list_spec_rule [l;n] mult_dist_right_suc_thm)
                           (list_spec_rule [l;`l*n`] add_comm_thm) );
                       (* |- ...                   <=> l * m < l * n          *)
                       list_spec_rule [`l*m`;`l*n`;l] add_lt_cancel_thm;
                       (* !n. l * m < l * n <=> m < n                         *)
                       (*      |- ...              <=> m < n                  *)
                       spec_rule n (assume_rule `!n. l * m < l * n <=> m < n`);
                       (* |- ...                   <=> SUC m < SUC n          *)
                       eq_sym_rule
                         (list_spec_rule [m;n] suc_lt_cancel_thm) ] )))
                 ))))))))
);;



(* ** LESS THAN OR EQUAL ** *)


(* Definition *)

set_fixity ("<=", Infix (40,NonAssoc));;

let le_def =
  new_fun_definition `!m n. m <= n <=> m < n \/ m = n`;;

let le_fn = `$<=`;;


(* Syntax functions *)

let dest_le = dest_cbin "<=";;

let mk_le (tm1,tm2) = mk_bin (le_fn,tm1,tm2);;

let is_le = can dest_le;;


(* le_cases_thm                                                               *)
(*                                                                            *)
(*    |- !m n. m <= n <=> m < n \/ m = n                                      *)

let le_cases_thm = save_thm ("le_cases_thm", le_def);;


(* le_refl_thm                                                                *)
(*                                                                            *)
(*    |- !n. n <= n                                                           *)

let le_refl_thm = save_thm ("le_refl_thm",
  gen_rule n
    (eq_mp_rule
      (* |- n < n \/ n = n <=> n <= n     *)
      (eq_sym_rule (list_spec_rule [n;n] le_cases_thm))
      (* |- n < n \/ n = n                *)
      (disj2_rule `n<n` (eq_refl_conv n)) )
);;


(* le_antisym_thm                                                             *)
(*                                                                            *)
(*    |- !m n. m <= n /\ n <= m ==> m = n                                     *)

let le_antisym_thm = save_thm ("le_antisym_thm",
  list_gen_rule [m;n]
    (disch_rule `m <= n /\ n <= m`
      (disj_cases_rule
        (* m <= n /\ n <= m |- (m < n /\ n < m) \/ m = n        *)
        (eq_mp_rule
          (eq_sym_rule
            (list_spec_rule [`m<n`;`n<m`;`(m:nat)=n`] disj_dist_left_conj_thm) )
          (* m <= n /\ n <= m |- (m < n \/ m = n) /\ (n < m \/ m = n)    *)
          (eq_mp_rule
            (mk_conj_rule
              (list_spec_rule [m;n] le_cases_thm)
              (eq_trans_rule
                (list_spec_rule [n;m] le_cases_thm)
                (mk_disj2_rule `n<m` (eq_sym_conv `(n:nat) = m`)) ))
            (assume_rule `m <= n /\ n <= m`) ))
        (* m < n /\ n < m |- m = n        *)
        (contr_rule `(m:nat)=n`
          (* m < n /\ n < m |- false        *)
          (undisch_rule
            (not_elim_rule (list_spec_rule [m;n] lt_asym_thm)) ))
        (* m = n |- m = n                 *)
        (assume_rule `(m:nat)=n`) ))
);;


(* le_trans_thm                                                               *)
(*                                                                            *)
(*    |- !l m n. l <= m /\ m <= n ==> l <= n                                  *)

let le_trans_thm = save_thm ("le_trans_thm",
  let th1 = assume_rule `l <= m /\ m <= n` in
  list_gen_rule [l;m;n]
    (disch_rule `l <= m /\ m <= n`
      (* l <= m /\ m <= n |- l <= m              *)
      (disj_cases_rule (* l <= m /\ m <= n |- l < m \/ l = m      *)
                       (eq_mp_rule (list_spec_rule [l;m] le_cases_thm)
                                   (conjunct1_rule th1) )
        (* l <= m /\ m <= n, l < m |- l <= n       *)
        (disj_cases_rule (* l <= m /\ m <= n |- m < n \/ m = n      *)
                         (eq_mp_rule (list_spec_rule [m;n] le_cases_thm)
                                     (conjunct2_rule th1) )
          (* l < m, m < n |- l <= n                  *)
          (eq_mp_rule
            (eq_sym_rule (list_spec_rule [l;n] le_cases_thm))
            (disj1_rule
              (* l < m, m < n |- l < n                   *)
              (mp_rule
                (list_spec_rule [l;m;n] lt_trans_thm)
                (conj_rule (assume_rule `l<m`) (assume_rule `m<n`)) )
              `(l:nat)=n` ) )
          (* l < m, m = n |- l <= n                  *)
          (mp_rule
            (eq_imp_rule2 (list_spec_rule [l;n] le_cases_thm))
            (disj1_rule
              (eq_mp_rule (mk_bin2_rule `$<` l (assume_rule `(m:nat)=n`))
                          (assume_rule `l<m`) )
              `(l:nat)=n` )))
        (* l <= m /\ m <= n, l = m |- l <= n       *)
        (disj_cases_rule (* l <= m /\ m <= n |- m < n \/ m = n      *)
                         (eq_mp_rule (list_spec_rule [m;n] le_cases_thm)
                                     (conjunct2_rule th1) )
          (* l = m, m < n |- l <= n                  *)
          (mp_rule
            (eq_imp_rule2 (list_spec_rule [l;n] le_cases_thm))
            (disj1_rule
              (eq_mp_rule
                (mk_bin1_rule `$<` (eq_sym_rule (assume_rule `(l:nat)=m`)) n)
                (assume_rule `m<n`) )
              `(l:nat) = n`))
          (* l = m, m = n |- l <= n                  *)
          (mp_rule
            (eq_imp_rule2 (list_spec_rule [l;n] le_cases_thm))
            (disj2_rule `l<n`
              (eq_trans_rule (assume_rule `(l:nat)=m`)
                             (assume_rule `(m:nat)=n`) ))))))
);;


(* le_zero_thm                                                                *)
(*                                                                            *)
(*    |- !n. n <= 0 <=> n = 0                                                 *)

let le_zero_thm = save_thm ("le_zero_thm",
  gen_rule n
    (list_eq_trans_rule
       [ (* |- n <= 0 <=> n < 0 \/ n = 0          *)
         list_spec_rule [n;`0`] le_cases_thm;
         (* |- ...    <=> n = 0                   *)
         mk_disj1_rule (eqf_intro_rule (spec_rule n not_lt_zero_thm)) `n=0`;
         list_spec_rule [`false`;`n=0`] disj_comm_thm;
         spec_rule `n=0` disj_id_thm ])
);;


(* zero_le_thm                                                                *)
(*                                                                            *)
(*    |- !n. 0 <= n                                                           *)

let zero_le_thm = save_thm ("zero_le_thm",
  gen_rule n
    (eq_mp_rule
      (* |- 0 < n \/ 0 = n <=> 0 <= n    *)
      (eq_sym_rule (list_spec_rule [`0`;n] le_cases_thm))
      (* |- 0 < n \/ 0 = n               *)
      (eq_mp_rule
        (eq_trans_rule (list_spec_rule [`n=0`;`0<n`] disj_comm_thm)
                       (mk_disj2_rule `0<n` (eq_sym_conv `n=0`)) )
        (spec_rule n lt_zero_cases_thm) ))
);;


(* suc_le_cancel_thm                                                          *)
(*                                                                            *)
(*    |- !m n. SUC m <= SUC n <=> m <= n                                      *)

let suc_le_cancel_thm = save_thm ("suc_le_cancel_thm",
  list_gen_rule [m;n]
    (list_eq_trans_rule
       [ (* |- SUC m <= SUC n <=> SUC m < SUC n \/ SUC m = SUC n    *)
         list_spec_rule [`SUC m`;`SUC n`] le_cases_thm;
         (* |- ...            <=> m < n \/ m = n                    *)
         mk_disj_rule (list_spec_rule [m;n] suc_lt_cancel_thm)
                      (list_spec_rule [m;n] suc_injective_thm);
         (* |- ...            <=> m <= n                            *)
         eq_sym_rule (list_spec_rule [m;n] le_cases_thm) ])
);;


(* add_le_cancel_thm                                                          *)
(*                                                                            *)
(*    |- !l m n. l + n <= m + n <=> l <= m                                    *)

let add_le_cancel_thm = save_thm ("add_le_cancel_thm",
  list_gen_rule [l;m;n]
    (list_eq_trans_rule
       [ (* |- l + n <= m + n <=> l + n < m + n \/ l + n = m + n    *)
         list_spec_rule [`l+n`;`m+n`] le_cases_thm;
         (* |- ...            <=> l < m \/ l = m                    *)
         mk_disj_rule (list_spec_rule [l;m;n] add_lt_cancel_thm)
                      (list_spec_rule [l;m;n] add_eq_cancel_thm);
         (* |- ...            <=> l <= m                            *)
         eq_sym_rule (list_spec_rule [l;m] le_cases_thm) ])
);;


(* mult_le_cancel_thm                                                         *)
(*                                                                            *)
(*    |- !l m n. ~ (l = 0) ==> l * m <= l * n <=> m <= n                      *)

let mult_le_cancel_thm = save_thm ("mult_le_cancel_thm",
  list_gen_rule [l;m;n]
    (disch_rule `~(l=0)`
      (list_eq_trans_rule
         [ (* |- l * m <= l * n <=> l * m < l * n \/ l * m = l * n    *)
           list_spec_rule [`l*m`;`l*n`] le_cases_thm;
           (* ~ (l = 0) |- ...  <=> l < m \/ l = m                    *)
           mk_disj_rule
             (undisch_rule (list_spec_rule [l;m;n] mult_lt_cancel_thm))
             (undisch_rule (list_spec_rule [l;m;n] mult_eq_cancel_thm));
           (* |- ...            <=> m <= n                            *)
           eq_sym_rule (list_spec_rule [m;n] le_cases_thm) ]))
);;


(* lt_suc_le_thm                                                              *)
(*                                                                            *)
(*    |- !m n. m < SUC n <=> m <= n                                           *)

let lt_suc_le_thm = save_thm ("lt_suc_le_thm",
  list_gen_rule [m;n]
    (list_eq_trans_rule
       [ (* |- m < SUC n <=> m < n \/ m = n         *)
         list_spec_rule [m;n] lt_suc_cases_thm;
         list_spec_rule [`(m:nat)=n`;`m<n`] disj_comm_thm;
         (* |- ...       <=> m <= n                 *)
         eq_sym_rule (list_spec_rule [m;n] le_cases_thm) ])
);;


(* suc_le_lt_thm                                                              *)
(*                                                                            *)
(*    |- !m n. SUC m <= n <=> m < n                                           *)

let suc_le_lt_thm = save_thm ("suc_le_lt_thm",
  gen_rule m
    (mp_rule
      (bspec_rule `\n. SUC m <= n <=> m < n` nat_induction_thm)
      (conj_rule
        (* |- SUC m <= 0 <=> m < 0                                            *)
        (list_eq_trans_rule
           [ (* |- SUC m <= 0 <=> SUC m = 0    *)
             spec_rule `SUC m` le_zero_thm;
             (* |- ...        <=> false        *)
             eqf_intro_rule (spec_rule m suc_not_zero_thm);
             (* |- ...        <=> m < 0        *)
             eq_sym_rule (eqf_intro_rule (spec_rule m not_lt_zero_thm)) ])
        (* |- !n. (SUC m <= n <=> m < n) ==> (SUC m <= SUC n <=> m < SUC n)   *)
        (gen_rule n
          (disch_rule `SUC m <= n <=> m < n`
            (eq_trans_rule
              (* |- SUC m <= SUC n <=> m <= n              *)
              (list_spec_rule [m;n] suc_le_cancel_thm)
              (* |- ...            <=> m < SUC n           *)
              (eq_sym_rule (list_spec_rule [m;n] lt_suc_le_thm) ))))))
);;


(* sub_floor_thm                                                              *)
(*                                                                            *)
(*    |- !m n. m <= n ==> m - n = 0                                           *)

let sub_floor_thm = save_thm ("sub_floor_thm",
  gen_rule m
    (mp_rule
      (bspec_rule `\n. m <= n ==> m - n = 0` nat_induction_thm)
      (conj_rule
        (* |- m <= 0 ==> m - 0 = 0                     *)
        (disch_rule `m <= 0`
          (eq_trans_rule
            (spec_rule m sub_right_id_thm)
            (eq_mp_rule
              (spec_rule m le_zero_thm)
              (assume_rule `m <= 0`) )))
        (gen_rule n
          (disch_rule `m <= n ==> m - n = 0`
            (disch_rule `m <= SUC n`
              (disj_cases_rule
                     (* m <= SUC n |- m < SUC n \/ m = SUC n    *)
                     (eq_mp_rule
                       (list_spec_rule [m;`SUC n`] le_cases_thm)
                       (assume_rule `m <= SUC n`) )
                (* ..., m < SUC n |- m - SUC n = 0                        *)
                (list_eq_trans_rule
                   [ (* |- m - SUC n = PRE (m - n)                            *)
                     list_spec_rule [m;n] (conjunct2_rule sub_def);
                     (* m <= n <=> m - n = 0, m < SUC n |- PRE m - n = PRE 0  *)
                     mk_comb2_rule `PRE`
                      (mp_rule
                        (assume_rule `m <= n ==> m - n = 0`)
                        (eq_mp_rule
                          (list_spec_rule [m;n] lt_suc_le_thm)
                          (assume_rule `m < SUC n`) ));
                     (* |- PRE 0 = 0                                          *)
                     pre_zero_thm ])
                (* m = SUC n |- m - SUC n = 0                             *)
                (eq_trans_rule
                  (eq_sym_rule (mk_bin2_rule `$-` m (assume_rule `m = SUC n`)))
                  (spec_rule m sub_cancel_thm) ))))) ))
);;



(* ** GREATER THAN ** *)


(* Definition *)

set_fixity (">", Infix (40,NonAssoc));;

let gt_def =
  new_fun_definition `!m n. m > n <=> n < m`;;

let gt_fn = `$>`;;


(* Syntax functions *)

let dest_gt = dest_cbin ">";;

let mk_gt (tm1,tm2) = mk_bin (gt_fn,tm1,tm2);;

let is_gt = can dest_gt;;



(* ** GREATER THAN OR EQUAL ** *)


(* Definition *)

set_fixity (">=", Infix (40,NonAssoc));;

let ge_def =
  new_fun_definition `!m n. m >= n <=> n <= m`;;

let ge_fn = `$>=`;;


(* Syntax functions *)

let dest_ge = dest_cbin ">=";;

let mk_ge (tm1,tm2) = mk_bin (ge_fn,tm1,tm2);;

let is_ge = can dest_ge;;


end;;
