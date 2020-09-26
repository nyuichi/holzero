(* ========================================================================== *)
(* NATURAL NUMBERS (HOL Zero)                                                 *)
(* - Theory defining natural numbers, plus basic derived properties           *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2010-2015                            *)
(* ========================================================================== *)


module Nat : Nat_sig = struct


(* This module extends the HOL logic with the theory of natural numbers.      *)
(* This involves giving theory entity definitions for the naturals base type  *)
(* and the "ZERO" and "SUC" constants, based on the theory of individuals,    *)
(* and proving a few important properties.                                    *)


open Def1;;
open Def2;;

open Equal;;
open EqCong;;
open Bool;;
open BoolAlg;;
open BoolClass;;

open Ind;;



(* ** NATURALS TYPE ** *)

(* Firstly a HOL base type for natural numbers, called "nat" and referred to  *)
(* as "the naturals", is defined.  This is done using the infinite type of    *)
(* individuals as the representation type.                                    *)


(* Characteristic funtion *)

(* "IsNatRep" is the characteristic function for the naturals base type,      *)
(* prescribing the subset of `:ind` used to represent naturals.  It is        *)
(* defined as the function that returns `true` for a given `:ind` element iff *)
(* any property that holds for "IND_ZERO" and all its successors under        *)
(* "IND_SUC" necessarily holds for the element.  This gives the smallest      *)
(* subset of `:ind` containing "IND_ZERO" and closed under "IND_SUC".         *)

let is_nat_rep_def =
  new_fun_definition
    `!(i:ind). IsNatRep i <=>
                   (!P. P IND_ZERO /\ (!j. P j ==> P (IND_SUC j)) ==> P i)`;;


(* ind_zero_is_nat_rep_lemma                                                  *)
(*                                                                            *)
(*    |- IsNatRep IND_ZERO                                                    *)

let ind_zero_is_nat_rep_lemma =
  let p = `P:ind->bool` in
  (* |- IsNatRep IND_ZERO           *)
  eq_mp_rule
    (* |- (!P. P IND_ZERO /\ (!j. P j ==> P (IND_SUC j)) ==> P IND_ZERO)   *)
    (*      <=> IsNatRep IND_ZERO                                          *)
    (eq_sym_rule (spec_rule `IND_ZERO` is_nat_rep_def))
    (* |- !P. P IND_ZERO /\ (!j. P j ==> P (IND_SUC j)) ==> P IND_ZERO     *)
    (gen_rule p
      (disch_rule `P IND_ZERO /\ (!j. P j ==> P (IND_SUC j))`
        (conjunct1_rule
          (assume_rule `P IND_ZERO /\ (!j. P j ==> P (IND_SUC j))`) )));;


(* ind_suc_is_nat_rep_lemma                                                   *)
(*                                                                            *)
(*    |- !i. IsNatRep i ==> IsNatRep (IND_SUC i)                              *)

let ind_suc_is_nat_rep_lemma =
  let p = `P:ind->bool` in
  let i = `i:ind` in
  (* |- !i. IsNatRep i ==> IsNatRep (IND_SUC i)           *)
  gen_rule i
    (disch_rule `IsNatRep i`
      (* IsNatRep i |- IsNatRep (IND_SUC i)                   *)
      (eq_mp_rule
        (eq_sym_rule (spec_rule `IND_SUC i` is_nat_rep_def))
        (* IsNatRep i |-                                                      *)
        (*    !P. P IND_ZERO /\ (!j. P j ==> P (IND_SUC j)) ==> P (IND_SUC i) *)
        (gen_rule p
          (disch_rule `P IND_ZERO /\ (!j. P j ==> P (IND_SUC j))`
            (mp_rule
              (* P IND_ZERO /\ (!j. P j ==> P (IND_SUC j)) |-                 *)
              (*                                        P i ==> P (IND_SUC i) *)
              (spec_rule i
                (conjunct2_rule
                  (assume_rule `P IND_ZERO /\ (!j. P j ==> P (IND_SUC j))`) ))
              (* P IND_ZERO /\ (!j. P j ==> P (IND_SUC j)), IsNatRep i |- P i *)
              (undisch_rule
                (spec_rule p
                  (eq_mp_rule
                    (spec_rule i is_nat_rep_def)
                    (assume_rule `IsNatRep i`) ))))))));;


(* nat_rep_exists_lemma                                                       *)
(*                                                                            *)
(*    |- ?x. IsNatRep x                                                       *)
(*                                                                            *)
(* This theorem shows that the characteristic function prescribes a non-empty *)
(* subset of individuals, and is the theorem supplied in the definition of    *)
(* the naturals type.                                                         *)

let nat_rep_exists_lemma =
  (* |- ?x. IsNatRep x        *)
  exists_rule (`?x. IsNatRep x`, `IND_ZERO`)
    (* |- IsNatRep IND_ZERO     *)
    ind_zero_is_nat_rep_lemma;;


(* Naturals type definition *)

(* The type for natural numbers can now be defined.                           *)

let nat_def = new_tyconst_definition ("nat", nat_rep_exists_lemma);;

let nat_ty = `:nat`;;


(* Naturals type bijections *)

let (nat_bij_def1,nat_bij_def2) =
  new_type_bijections "nat" ("NatAbs","NatRep");;
               (* |- !a. NatAbs (NatRep a) = a                   *)
               (* |- !r. IsNatRep r <=> NatRep (NatAbs r) = r    *)


(* is_nat_rep_lemma : thm                                                     *)
(*                                                                            *)
(*    |- !n. IsNatRep (NatRep n)                                              *)

let is_nat_rep_lemma =
  let n = `n:nat` in
  (* |- !n. IsNatRep (NatRep n)            *)
  gen_rule n
    (eq_mp_rule
      (* |- NatRep (NatAbs (NatRep n)) = NatRep n <=> IsNatRep (NatRep n)  *)
      (eq_sym_rule (spec_rule `NatRep n` nat_bij_def2))
      (mk_comb2_rule `NatRep`
        (spec_rule `n:nat` nat_bij_def1) ));;


(* nat_rep_injective_lemma : thm                                              *)
(*                                                                            *)
(*    |- !m n. NatRep m = NatRep n <=> m = n                                  *)

let nat_rep_injective_lemma =
  let m = `m:nat` and n = `n:nat` in
  (* |- !m n. NatRep m = NatRep n <=> m = n      *)
  list_gen_rule [m;n]
    (deduct_antisym_rule
      (* m = n |- NatRep m = NatRep n                *)
      (mk_comb2_rule `NatRep` (assume_rule `(m:nat) = n`))
      (* NatRep m = NatRep n |- m = n                *)
      (eq_mp_rule
        (* |- NatAbs (NatRep m) = NatAbs (NatRep n) <=> m = n             *)
        (mk_eq_rule
          (spec_rule m nat_bij_def1)
          (spec_rule n nat_bij_def1) )
        (* NatRep m = NatRep n |- NatAbs (NatRep m) = NatAbs (NatRep n)   *)
        (mk_comb2_rule `NatAbs` (assume_rule `NatRep m = NatRep n`)) ));;



(* ** ZERO AND SUC ** *)

(* The constants "ZERO" and "SUC" are now defined in terms of their           *)
(* equivalents in the individuals type, and some basic properties are proved. *)


(* Definitions *)

let zero_def = new_const_definition `ZERO = NatAbs IND_ZERO`;;

let zero_tm0 = `ZERO`;;

let suc_def = new_fun_definition `!n. SUC n = NatAbs (IND_SUC (NatRep n))`;;

let suc_fn = `SUC`;;


(* Syntax functions *)

let mk_suc tm =
  let () = assert1 (type_of tm = nat_ty)   ("mk_suc", "Not a natural number") in
  mk_comb (suc_fn,tm);;

let dest_suc tm =
 try
  let (tm1,tm2) = dest_comb tm in
  let () = assert0 (tm1 = suc_fn)      LocalFail in
  tm2
 with HolFail _ | LocalFail -> hol_fail ("dest_suc", "Not a SUC expression");;

let is_suc tm = can dest_suc tm;;


(* nat_rep_zero_lemma : thm                                                   *)
(*                                                                            *)
(*    |- NatRep ZERO = IND_ZERO                                               *)

let nat_rep_zero_lemma =
  (* |- NatRep ZERO = IND_ZERO                   *)
  eq_trans_rule
    (* |- NatRep ZERO = NatRep (NatAbs IND_ZERO)   *)
    (mk_comb2_rule `NatRep` zero_def)
    (* |- NatRep (NatAbs IND_ZERO) = IND_ZERO      *)
    (eq_mp_rule
      (spec_rule `IND_ZERO` nat_bij_def2)
      ind_zero_is_nat_rep_lemma );;


(* nat_rep_suc_lemma : thm                                                    *)
(*                                                                            *)
(*    |- !n. NatRep (SUC n) = IND_SUC (NatRep n)                              *)

let nat_rep_suc_lemma =
  let n = `n:nat` in
  (* |- !n. NatRep (SUC n) = IND_SUC (NatRep n)           *)
  gen_rule n
    (eq_trans_rule
      (* |- NatRep (SUC n) = NatRep (NatAbs (IND_SUC (NatRep n)))      *)
      (mk_comb2_rule `NatRep`
        (spec_rule n suc_def) )
      (* |- NatRep (NatAbs (IND_SUC (NatRep n))) = IND_SUC (NatRep n)  *)
      (eq_mp_rule
        (spec_rule `IND_SUC (NatRep n)` nat_bij_def2)
        (* |- IsNatRep (IND_SUC (NatRep n))                              *)
        (mp_rule
          (spec_rule `NatRep n` ind_suc_is_nat_rep_lemma)
          (spec_rule n is_nat_rep_lemma) )));;


(* suc_not_zero_thm0 : thm                                                    *)
(*                                                                            *)
(*    |- !n. ~ (SUC n = ZERO)                                                 *)

let suc_not_zero_thm0 =
  let n = `n:nat` in
  (* |- !n. ~ (SUC n = ZERO)                *)
  gen_rule n
    (not_intro_rule
      (disch_rule `SUC n = ZERO`
        (* SUC n = ZERO |- false                           *)
        (eq_mp_rule
          (* |- NatRep (SUC n) = NatRep ZERO <=> false       *)
          (eq_trans_rule
            (* |- NatRep (SUC n) = NatRep ZERO <=>             *)
            (*                 IND_SUC (NatRep n) = IND_ZERO   *)
            (mk_eq_rule
              (spec_rule n nat_rep_suc_lemma)
              nat_rep_zero_lemma )
            (* |- IND_SUC (NatRep n) = IND_ZERO <=> false      *)
            (eqf_intro_rule
              (spec_rule `NatRep n` ind_suc_not_zero_thm) ))
          (* SUC n = ZERO |- NatRep (SUC n) = NatRep ZERO    *)
          (mk_comb2_rule `NatRep` (assume_rule `SUC n = ZERO`) ))));;


(* suc_injective_thm : thm                                                    *)
(*                                                                            *)
(*    |- !m n. SUC m = SUC n <=> m = n                                        *)

let suc_injective_thm = save_thm ("suc_injective_thm",
  let m = `m:nat` and n = `n:nat` in
  (* !m n. SUC m = SUC n <=> m = n                           *)
  list_gen_rule [m;n]
    (list_eq_trans_rule [
      (* |- SUC m = SUC n <=> NatRep (SUC m) = NatRep (SUC n)           *)
      eq_sym_rule (list_spec_rule [`SUC m`;`SUC n`] nat_rep_injective_lemma);
      (* |- ...           <=> IND_SUC (NatRep m) = IND_SUC (NatRep n)   *)
      mk_eq_rule
        (spec_rule m nat_rep_suc_lemma)
        (spec_rule n nat_rep_suc_lemma);
      (* |- ...           <=> NatRep m = NatRep n                       *)
      list_spec_rule [`NatRep m`;`NatRep n`] ind_suc_injective_thm;
      (* |- ...           <=> m = n                                     *)
      list_spec_rule [m;n] nat_rep_injective_lemma
      ])
);;



(* ** INDUCTION AND CASES ** *)

(* Now we can prove two important general properites about natural numbers.   *)


(* nat_induction_thm0 : thm                                                   *)
(*                                                                            *)
(*    |- !P. P ZERO /\ (!n. P n ==> P (SUC n)) ==> (!n. P n)                  *)

let nat_induction_thm0 =
  let j = `j:ind` and n = `n:nat` and p = `P:nat->bool` in
  let th1 = assume_rule `P ZERO /\ (!n. P n ==> P (SUC n))` in
  let th2 = assume_rule `IsNatRep j /\ P (NatAbs j)` in
  (* |- !P. P ZERO /\ (!n. P n ==> P (SUC n)) ==> (!n. P n)    *)
  gen_rule p
    (disch_rule `P ZERO /\ (!n. P n ==> P (SUC n))`
      (gen_rule n
        (* P ZERO /\ (!n. P n ==> P (SUC n)) |- P n               *)
        (eq_mp_rule
          (* |- P (NatAbs (NatRep n)) <=> P n                            *)
          (mk_comb2_rule p (spec_rule n nat_bij_def1))
          (conjunct2_rule
            (* P ZERO /\ (!n. P n ==> P (SUC n))                            *)
            (*    |- IsNatRep (NatRep n) /\ P (NatAbs (NatRep n))           *)
            (mp_rule
              (bspec_rule `\i. IsNatRep i /\ (P:nat->bool) (NatAbs i)`
                (* |- !P. P IND_ZERO /\ (!j. P j ==> P (IND_SUC j))           *)
                (*        ==> P (NatRep n))                                   *)
                (eq_mp_rule
                  (spec_rule `NatRep n` is_nat_rep_def)
                  (spec_rule n is_nat_rep_lemma) ))
              (conj_rule
                (* P ZERO /\ (!n. P n ==> P (SUC n))                      *)
                (*    |- IsNatRep IND_ZERO /\ P (NatAbs IND_ZERO)         *)
                (eq_mp_rule
                  (mk_conj2_rule `IsNatRep IND_ZERO`
                    (mk_comb2_rule p zero_def) )
                  (conj_rule ind_zero_is_nat_rep_lemma (conjunct1_rule th1)) )
                (* P ZERO /\ (!n. P n ==> P (SUC n))                          *)
                (*    |- !j. IsNatRep j /\ P (NatAbs j)                       *)
                (*           ==> IsNatRep(IND_SUC j) /\ P (NatAbs(IND_SUC j)) *)
                (gen_rule j
                  (disch_rule `IsNatRep j /\ P (NatAbs j)`
                    (conj_rule
                      (* IsNatRep j /\ P (NatAbs j) |- IsNatRep (IND_SUC j)   *)
                      (mp_rule
                        (spec_rule j ind_suc_is_nat_rep_lemma)
                        (conjunct1_rule th2) )
                      (* P ZERO /\ (!n. P n ==> P (SUC n)),                   *)
                      (*   IsNatRep j /\ P (NatAbs j) |- P (NatAbs(IND_SUC j))*)
                      (eq_mp_rule
                        (* IsNatRep j /\ P (NatAbs j)                         *)
                        (*   |- P (SUC (NatAbs j)) <=> P (NatAbs (IND_SUC j)) *)
                        (mk_comb2_rule p
                          (eq_trans_rule
                            (* |- SUC (NatAbs j) =                            *)
                            (*       NatAbs (IND_SUC (NatRep (NatAbs j)))     *)
                            (spec_rule `NatAbs j` suc_def)
                            (mk_comb2_rule `NatAbs`
                              (mk_comb2_rule `IND_SUC`
                                (* IsNatRep j /\ P (NatAbs j)                 *)
                                (*     |- NatRep (NatAbs j) = j               *)
                                (eq_mp_rule
                                  (spec_rule j nat_bij_def2)
                                  (conjunct1_rule th2) )))))
                        (* !n. P n ==> P (SUC n), IsNatRep j /\ P (NatAbs j)  *)
                        (*    |- P (SUC (NatAbs j))                           *)
                        (mp_rule
                          (* !n. P n ==> P (SUC n)                            *)
                          (*    |- P (NatAbs j) ==> P (SUC (NatAbs j))        *)
                          (spec_rule `NatAbs j` (conjunct2_rule th1))
                          (conjunct2_rule th2) )))))))))));;


(* nat_cases_thm0 : thm                                                       *)
(*                                                                            *)
(*    |- !n. n = ZERO \/ (?m. n = SUC m)                                      *)

let nat_cases_thm0 =
  let n = `n:nat` in
  (* |- !n. n = ZERO \/ (?m. n = SUC m)                      *)
  mp_rule
    (bspec_rule `\n. n = ZERO \/ (?m. n = SUC m)` nat_induction_thm0)
    (conj_rule
      (* |- ZERO = ZERO \/ (?n. ZERO = SUC n)                     *)
      (disj1_rule (eq_refl_conv `ZERO`) `?n. ZERO = SUC n`)
      (* |- !n. n = ZERO \/ (?m. n = SUC m)                       *)
      (*        ==> SUC n = ZERO \/ (?m. SUC n = SUC m)           *)
      (gen_rule n
        (disch_rule `n = ZERO \/ (?m. n = SUC m)`
          (* |- SUC n = ZERO \/ (?m. SUC n = SUC m)                   *)
          (disj2_rule `SUC n = ZERO`
            (exists_rule (`?m. SUC n = SUC m`, n)
              (eq_refl_conv `SUC n`) )))));;



(* ** PRIMITIVE RECURSION THEOREM ** *)

(* This final section proves the primitive recursion theorem for natural      *)
(* numbers.  This is a crucial theorem which, when supplied to the recursive  *)
(* definition command, enables intuitive recursive-style definitions to be    *)
(* provided for the arithmetic operators.                                     *)

(* The theorem states that, given some recursive-style definition of a        *)
(* function over natural numbers, there exists a function that satifies this  *)
(* definition.                                                                *)
(*    |- !e f. ?fn. fn ZERO = e /\ (!n. fn (SUC n) = f (fn n) n)              *)

(* The proof is based on HOL Light's (although HOL Light first proves a       *)
(* stronger property - that the function exists and is unique).  The proof is *)
(* quite substantial, and is broken down into 4 lemmas.                       *)


(* HOL variables *)

(* ML names are given here for the various HOL variables used in the          *)
(* statement and proof of the theorem.                                        *)

let e = `e:'a` and f = `f:'a->nat->'a`;;
let fn_ = `fn:nat->'a`;;

let prg = `PRG:nat->'a->bool` and prg' = `PRG':nat->'a->bool`;;
let m = `m:nat` and n = `n:nat` and n' = `n':nat`;;
let x = `x:'a` and x' = `x':'a`;;
let y = `y:'a` and y1 = `y1:'a` and y2 = `y2:'a`;;

let f_x_n = `(f:'a->nat->'a) x n`;;
let f_y_n = `(f:'a->nat->'a) y n`;;
let prg_n_x = `(PRG:nat->'a->bool) n x`;;
let fn_n = `(fn:nat->'a) n`;;


(* Intermediate assumptions *)

let prg_case1_tm = `m = ZERO /\ (y:'a) = e`;;
let prg_case2_tm_body_tm = `m = SUC n /\ y = (f:'a->nat->'a) x n /\ PRG n x`;;
let prg_case2_tm_body1_tm = `?n. m = SUC n /\ (y:'a) = f (x:'a) n /\ PRG n x`;;
let prg_case2_tm = `?(x:'a) n. m = SUC n /\ (y:'a) = f x n /\ PRG n x`;;

let prg_casesdef_body =
  `m = ZERO /\ (y:'a) = e \/
   (?(x:'a) n. m = SUC n /\ (y:'a) = f x n /\ PRG n x)`;;

let prg_casesdef_tm =
  `!(m:nat) (y:'a).
      PRG m y <=>
         m = ZERO /\ y = e \/
         (?x n. m = SUC n /\ y = f x n /\ PRG n x)`;;

let prg_casesdef_weak_tm =
  `!(m:nat) (y:'a).
      m = ZERO /\ y = e \/
      (?(x:'a) n. m = SUC n /\ y = f x n /\ PRG n x)
      ==> PRG m y`;;

let prg'_casesdef_weak_tm =
  `!(m:nat) (y:'a).
      m = ZERO /\ y = e \/
      (?(x:'a) n. m = SUC n /\ y = f x n /\ PRG' n x)
      ==> PRG' m y`;;

let prg_recdef_tm =
  `PRG ZERO e /\ (!(x:'a) n. PRG n x ==> PRG (SUC n) (f x n))`;;

let prg_defconj_tm = mk_conj (prg_recdef_tm,prg_casesdef_tm);;
let exists_prg_defconj_tm = mk_exists (prg,prg_defconj_tm);;

let prg_fpdef_tm =
  `!(m:nat) (y:'a). PRG m y <=>
       (!PRG'. (!(m:nat) (y:'a).
                   m = ZERO /\ y = e \/
                   (?x n. m = SUC n /\ y = f x n /\ PRG' n x)
                   ==> PRG' m y)
               ==> PRG' m y)` ;;


(* Lemma 1 *)

(* This establishes a property used twice in Lemma 2:                         *)
(*   |- !PRG PRG'.                                                            *)
(*         (!m y. PRG m y ==> PRG' m y)                                       *)
(*         ==> (!m y.                                                         *)
(*                 m = ZERO /\ y = e \/                                       *)
(*                 (?x n. m = SUC n /\ y = f x n /\ PRG n x)                  *)
(*                 ==> m = ZERO /\ y = e \/                                   *)
(*                     (?x n. m = SUC n /\ y = f x n /\ PRG' n x))            *)

let lemma1 =
  let tm1a = `!(m:nat) (y:'a). PRG m y ==> PRG' m y` in
  let tm1b = `?(x:'a) n. m = SUC n /\ (y:'a) = f x n /\ PRG' n x` in
  list_gen_rule [prg;prg'] (disch_rule tm1a
   (list_gen_rule [m;y] (disch_rule prg_casesdef_body
     (disj_cases_rule (assume_rule prg_casesdef_body)
       (disj1_rule (assume_rule prg_case1_tm) tm1b)
       (disj2_rule prg_case1_tm
         (choose_rule (x, assume_rule prg_case2_tm)
           (choose_rule (n, assume_rule prg_case2_tm_body1_tm)
             (exists_rule (tm1b, x)
               (exists_rule
                      (`?n. m = SUC n /\ (y:'a) = f (x:'a) n /\ PRG' n x`,n)
                 (conj_rule
                   (conjunct1_rule (assume_rule prg_case2_tm_body_tm))
                   (conj_rule
                     (conjunct1_rule
                       (conjunct2_rule (assume_rule prg_case2_tm_body_tm)))
                     (mp_rule
                       (spec_rule x (spec_rule n (assume_rule tm1a)))
                       (conjunct2_rule
                         (conjunct2_rule
                           (assume_rule prg_case2_tm_body_tm) )))))))))))))) ;;


(* Lemma 2 *)

(* This establishes that there exists some relation 'PRG' that satisifies     *)
(* both a recursive-style def and a cases-style def:                          *)
(*   |- ?PRG.                                                                 *)
(*        (PRG ZERO e /\                                  <PRG-rec-def>       *)
(*         (!x n. PRG n x ==> PRG (SUC n) (f x n))) /\                        *)
(*        (!m y.                                          <PRG-cases-def>     *)
(*            PRG m y <=>                                                     *)
(*            m = ZERO /\ y = e \/ (?x n. m = SUC n /\ y = f x n /\ PRG n x)) *)

let lemma2 =
  let tm2 = `!PRG'. (!m (y:'a). m = ZERO /\ y = e \/
                               (?(x:'a) n. m = SUC n /\ y = f x n /\ PRG' n x)
                               ==> PRG' m y)
                    ==> PRG' m y` in
  let tm2a = mk_abs (y,tm2) in
  let tm2b = mk_abs (m,tm2a) in
  let tm2c = mk_comb (tm2b,m) in
  let tm2d = mk_comb (tm2a,y) in
  let tm2e = `\(m:nat) (y:'a).
                 m = ZERO /\ y = e \/
                 (?(x:'a) n. m = SUC n /\ y = f x n /\ PRG n x)` in
  let tm2f = `(?(x:'a) n. m = SUC n /\ (y:'a) = f x n /\ PRG n x) ==> PRG m y`in
  let th2a = disch_rule prg_casesdef_weak_tm
               (undisch_rule
                 (list_spec_rule [m;y] (assume_rule prg_casesdef_weak_tm))) in
  let th2b = list_spec_rule [m;y] (assume_rule prg_fpdef_tm) in
  let th2c = (* <PRG-fpdef>,                                        *)
             (* <PRG'-casesdef-weak>                                *)
             (* |- !m y. PRG m y ==> PRG' m y                       *)
             list_gen_rule [m;y]
              (disch_rule `(PRG:nat->'a->bool) m y`
                (undisch_rule
                  (spec_rule prg' (undisch_rule (eq_imp_rule1 th2b))) )) in
  let th2d = (* <PRG-fpdef>                                         *)
             (* |- <PRG-casesdef-weak>                              *)
             list_gen_rule [m;y]
              (disch_rule prg_casesdef_body
                (eq_mp_rule
                  (eq_sym_rule th2b)
                  (gen_rule prg' (disch_rule prg'_casesdef_weak_tm
                    (mp_rule
                      (list_spec_rule [m;y] (assume_rule prg'_casesdef_weak_tm))
                      (undisch_rule
                        (list_spec_rule [m;y]
                          (mp_rule (list_spec_rule [prg;prg'] lemma1)
                                   th2c )) )))))) in

  (* |- ?PRG. <PRG-rec-def> /\ <PRG-cases-def>      *)
  choose_rule (prg,

    (* |- ?PRG. <PRG-fpdef>                            *)
    exists_rule (mk_exists(prg,prg_fpdef_tm), tm2b)
     (list_gen_rule [m;y]
       (eq_trans_rule
         (mk_comb1_rule (beta_conv tm2c) y)
         (beta_conv tm2d) )) )

   (* <PRG-fpdef>                                     *)
   (* |- ?PRG. <PRG-rec-def> /\ <PRG-cases-def>       *)
   (exists_rule (exists_prg_defconj_tm,prg)
     (conj_rule

       (* <PRG-fpdef>                                     *)
       (* |- <PRG-rec-def>                                *)
       (prove_asm_rule

         th2d

         (* <PRG-casesdef-weak>                               *)
         (* |- PRG ZERO e /\                    <PRG-rec-def> *)
         (*    (!x n. PRG n x ==> PRG (SUC n) (f x n))        *)
         (conj_rule
           (mp_rule (inst_rule [(m,`ZERO`);(y,e)]
                  (disch_rule prg_case1_tm (undisch_rule
                    (prove_asm_rule
                      (disj1_rule (assume_rule prg_case1_tm) prg_case2_tm)
                      th2a ) )))
               (conj_rule (eq_refl_conv `ZERO`) (eq_refl_conv e)) )
           (list_gen_rule [x;n] (disch_rule prg_n_x
             (mp_rule (inst_rule [(m,`SUC n`);(y,f_x_n)]
                   (prove_asm_rule
                     (disch_rule prg_case2_tm (undisch_rule
                       (prove_asm_rule
                         (disj2_rule prg_case1_tm (assume_rule prg_case2_tm))
                         th2a) ))
                     (disch_rule prg_case2_tm_body_tm
                       (mp_rule (assume_rule tm2f)
                           (exists_rule (prg_case2_tm,x)
                             (exists_rule (prg_case2_tm_body1_tm,n)
                               (assume_rule prg_case2_tm_body_tm))) ) )))
                 (conj_rule (eq_refl_conv `SUC n`)
                   (conj_rule (eq_refl_conv f_x_n)
                              (assume_rule prg_n_x))) ))) ))

       (* <PRG-fpdef>                                     *)
       (* |- <PRG-cases-def>                              *)
       (list_gen_rule [m;y]
         (imp_antisym_rule
           (list_spec_rule [m;y]
             (mp_rule
               (bspec_rule tm2e
                 (gen_rule prg' (disch_rule prg'_casesdef_weak_tm th2c)) )
               (mp_rule (list_bspec_rule [tm2e;prg] lemma1)
                        th2d )))
           (list_spec_rule [m;y] th2d) ))));;


(* Lemma 3 *)

(* This uses induction to prove that some given relation 'PRG' is functional  *)
(* under an assumption giving a cases-style definition of 'PRG':              *)
(*   !m y.                                                <PRG-cases-def>     *)
(*      PRG m y <=>                                                           *)
(*      m = ZERO /\ y = e \/ (?x n. m = SUC n /\ y = f x n /\ PRG n x))       *)
(*   |- !n. ?!y. PRG n y                                  <PRG-functional>    *)

let lemma3 =

  let tm3a = `?!(x:'a). PRG (n:nat) x` in
  let tm3b = `y = (f:'a->nat->'a) x n /\ PRG n x` in
  let tm3c = `(?(x:'a). (y1:'a) = f x (n:nat) /\ PRG n x) /\
              (?x. y2 = f x n /\ PRG n x)` in
  let tm3d = `(y:'a) = e` in
  let tm3e = `?(x:'a) (n':nat).
                 n' = n /\ y = (f:'a->nat->'a) x n' /\ PRG n' x` in
  let th3a = assume_rule `y1 = (f:'a->nat->'a) x n /\ PRG n x` in
  let th3b = assume_rule `y2 = (f:'a->nat->'a) x' n /\ PRG n x'` in
  let th3c = assume_rule tm3c in
  let th3d = spec_rule `false` exists_null_thm in(* |- (?x. false) <=> false  *)
  let th3e = eqf_intro_rule                      (* |- SUC n = ZERO <=> false *)
               (spec_rule n suc_not_zero_thm0) in
  let th3f = eq_mp_rule
               (bspec_rule `\x. (PRG:nat->'a->bool) n x` uexists_thm3)
               (assume_rule tm3a) in
  let th3g = assume_rule prg_casesdef_tm in

  mp_rule

   (bspec_rule `\(n:nat). ?!(y:'a). PRG n y`
     (* |- !P. P ZERO /\ (!n. P n ==> P (SUC n)) ==> (!n. P n)    *)
     nat_induction_thm0 )

   (conj_rule

     (* Base Case:                                    *)
     (*   <PRG-cases-def>                             *)
     (*   |- ?!y. PRG ZERO y                          *)
     (eq_mp_rule
       (eq_sym_rule
         (mk_uexists_rule y
           (* <PRG-cases-def>                               *)
           (* |- PRG ZERO y <=> y = e                       *)
           (list_eq_trans_rule [
              list_spec_rule [`ZERO`;y] th3g;
              mk_disj_rule
               (list_eq_trans_rule
                  [ mk_conj1_rule (eqt_intro_rule (eq_refl_conv `ZERO`)) tm3d;
                    list_spec_rule [`true`;tm3d] conj_comm_thm;
                    spec_rule tm3d conj_id_thm ] )
               (eq_trans_rule (mk_exists_rule x
                 (eq_trans_rule (mk_exists_rule n
                   (list_eq_trans_rule
                      [ mk_conj1_rule
                         (eq_trans_rule (eq_sym_conv `ZERO = SUC n`) th3e)
                         tm3b;
                        list_spec_rule [`false`;tm3b] conj_comm_thm;
                        spec_rule tm3b conj_zero_thm ] ))
                   (inst_type_rule [a_ty,nat_ty] th3d) ))
                 th3d );
              spec_rule tm3d disj_id_thm ] )) )
       (* |- ?!x. x = e             *)
       (eqt_elim_rule
         (eq_trans_rule
           (eq_sym_rule (mk_uexists_rule x (spec_rule `(x:'a)=e` conj_id_thm)))
           (list_bspec_rule [`\(x:'a).true`;e] uexists_one_point_thm) )))

     (* Step Case:                                          *)
     (*   <PRG-cases-def>                                   *)
     (*   |- !n. (?!x. PRG n x) ==> (?!x. PRG (SUC n) x)    *)
     (gen_rule n
       (disch_rule tm3a
         (eq_mp_rule
           (eq_sym_rule
             (mk_uexists_rule y
               (* <PRG-cases-def>                                     *)
               (* |- PRG (SUC n) y <=> (?x. y = f x n /\ PRG n x)     *)
               (list_eq_trans_rule
                  [ list_spec_rule [`SUC n`;y] th3g;
                    mk_disj_rule
                     (list_eq_trans_rule
                        [ mk_conj1_rule th3e tm3d;
                          list_spec_rule [`false`;tm3d] conj_comm_thm;
                          spec_rule tm3d conj_zero_thm ])
                     (mk_exists_rule x
                       (mk_exists_rule n'
                         (mk_conj1_rule
                           (eq_trans_rule
                             (list_spec_rule [n;n'] suc_injective_thm)
                             (eq_sym_conv `(n:nat) = n'`) )
                           `y = (f:'a->nat->'a) x n' /\ PRG n' x` )));
                    list_spec_rule [`false`;tm3e] disj_comm_thm;
                    spec_rule tm3e disj_id_thm;
                    mk_exists_rule x
                     (list_bspec_rule
                        [`\(n':nat). (y:'a) = f (x:'a) n' /\ PRG n' x`;n]
                        (inst_type_rule [a_ty,nat_ty] exists_one_point_thm) ) ])
               ))
           (* ?!x. PRG n x |- ?!y. ?x. y = f x n /\ PRG n x       *)
           (eq_mp_rule
             (eq_sym_rule
               (bspec_rule `\(y:'a). ?(x:'a). y = f x (n:nat) /\ PRG n x`
                           uexists_thm3))
             (conj_rule
               (choose_rule (y, conjunct1_rule th3f)
                 (exists_rule
                         (`?(y:'a) (x:'a). y = f x (n:nat) /\ PRG n x`,f_y_n)
                   (exists_rule
                         (`?(x:'a). (f:'a->nat->'a) y n = f x n /\ PRG n x`,y)
                     (conj_rule (eq_refl_conv f_y_n)
                                (assume_rule `(PRG:nat->'a->bool) n y`)) )))
               (list_gen_rule [y1;y2] (disch_rule tm3c
               (choose_rule (x, conjunct1_rule th3c)
                 (choose_rule (x', conjunct2_rule th3c)
                   (eq_mp_rule
                     (eq_sym_rule (mk_eq_rule (conjunct1_rule th3a)
                                              (conjunct1_rule th3b) ))
                   (mk_comb1_rule (mk_comb2_rule f
                     (mp_rule
                       (list_spec_rule [x;x'] (conjunct2_rule th3f))
                       (conj_rule (conjunct2_rule th3a)
                                  (conjunct2_rule th3b)) ) ) n)) )))) ))))) ) ;;


(* Lemma 4 *)

(* This establishes the main goal under two assumptions about some given      *)
(* relation 'PRG':                                                            *)
(*   PRG ZERO e /\ (!x n. PRG n x ==> PRG (SUC n) (f x n)), <PRG-rec-def>     *)
(*   !n. ?!x. PRG n x                                       <PRG-functional>  *)
(*   |- ?fn. fn ZERO = e /\ (!n. fn (SUC n) = f (fn n) n)                     *)

let lemma4 =
  let th4a = assume_rule `!(n:nat) (y:'a). PRG n y <=> fn n = y` in
  let th4b = assume_rule prg_recdef_tm in
  choose_rule (fn_,
    undisch_rule
     (eq_imp_rule1
       (spec_rule prg
         (inst_type_rule [(b_ty,a_ty);(a_ty,nat_ty)] unique_skolem_thm)) ) )
   (exists_rule
         (`?fn. fn ZERO = e /\
                (!n. fn (SUC n) = (f:'a->nat->'a) (fn n) n)`, fn_)
     (conj_rule
       (eq_mp_rule (list_spec_rule [`ZERO`;e] th4a)
                   (conjunct1_rule th4b) )
       (gen_rule n
         (eq_mp_rule
           (list_spec_rule [`SUC n`;`(f:'a->nat->'a) (fn n) n`] th4a)
           (mp_rule (list_spec_rule [fn_n;n] (conjunct2_rule th4b))
              (eq_mp_rule (eq_sym_rule (list_spec_rule [n;fn_n] th4a))
                 (eq_refl_conv fn_n) )))) ));;


(* nat_recursion_thm0 : thm                                                   *)
(*                                                                            *)
(*    |- !e f. ?fn. fn ZERO = e /\ (!n. fn (SUC n) = f (fn n) n)              *)

let nat_recursion_thm0 =

  let th1 = assume_rule prg_defconj_tm in

  list_gen_rule [e;f]

   (* Use Lemma 2 to discharge the existential conjunction asm:      *)
   (*   |- ?fn. fn ZERO = e /\ (!n. fn (SUC n) = f (fn n) n)         *)
   (prove_asm_rule

     lemma2

     (* Wrap up the PRG def asms into an existential conjunction:      *)
     (*   ?PRG. <PRG-rec-def> /\ <PRG-cases-def>                       *)
     (*   |- ?fn. fn ZERO = e /\ (!n. fn (SUC n) = f (fn n) n)         *)
     (choose_rule (prg, assume_rule exists_prg_defconj_tm)
       (prove_asm_rule (conjunct1_rule th1)
         (prove_asm_rule (conjunct2_rule th1)

           (* Use Lemma 3 to replace Lemma 4's PRG-functional asm with a  *)
           (* PRG-cases-style def asm:                                    *)
           (*   <PRG-cases-def>                                           *)
           (*   <PRG-rec-def>                                             *)
           (*   |- ?fn. fn ZERO = e /\ (!n. fn (SUC n) = f (fn n) n)      *)
           (prove_asm_rule
             lemma3
             lemma4) ))) )


end;;
