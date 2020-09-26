(* ========================================================================== *)
(* INDIVIDUALS (HOL Zero)                                                     *)
(* - Theory asserting the existence of an infinite type                       *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2015                            *)
(* ========================================================================== *)


module Ind : Ind_sig = struct


(* This module extends the HOL logic with an infinite-cardinality base type,  *)
(* together with a zero and a successor function for this type.  These get    *)
(* used in the 'Nat' module as the basis for defining the natural numbers.    *)


open Def1;;

open Equal;;
open EqCong;;
open Bool;;
open BoolClass;;



(* ** INDIVIDUALS TYPE ** *)

(* An infinite-cardinality base type, called "ind" and referred to as "the    *)
(* individuals type", is introduced and asserted (by axiom) to have infinite  *)
(* cardinality.                                                               *)


(* Individuals type *)

let ind_ty = new_tyconst ("ind",0);;


(* Infinity axiom *)

(* This states that the newly declared individuals type is infinite, by       *)
(* asserting that there is an injective total function from individuals to    *)
(* individuals that is not surjective.                                        *)

let infinity_ax =
  new_axiom ("infinity_ax", `?(f:ind->ind). ONE_ONE f /\ ~ ONTO f`);;



(* ** IND_ZERO AND IND_SUC ** *)

(* The successor function for "ind" ("IND_SUC") is defined as an injective,   *)
(* non-surjective function on "ind" (asserted to exist by the Infinity        *)
(* axiom).  The zero element for "ind" ("IND_ZERO") is defined as an element  *)
(* that "IND_SUC" does not map to.  These are defined by constant             *)
(* specification.  Then a few basic properties are proved.                    *)


(* Existence lemma *)

(* It's first necessary to prove a lemma explicitly stating the existence of  *)
(* of "IND_SUC" and "IND_ZERO", to supply to the constant specification       *)
(* command.                                                                   *)

(* not_onto_lemma : thm                                                       *)
(*                                                                            *)
(*    |- !f. ~ ONTO f <=> ?y. !x. ~(f x = y)                                  *)

let not_onto_lemma =
  let f = `f:'a->'b` and x = `x:'a` and y = `y:'b` in
  (* |- !f. ~ ONTO f <=> ?y. !x. ~(f x = y)         *)
  gen_rule f
    (list_eq_trans_rule [
      (* |- ~ ONTO f <=> ~(!y. ?x. y = f x)             *)
      mk_comb2_rule `$~` (app_beta_rhs_rule onto_def f);
      (* |- ~ (!y. ?x. y = f x) <=> (?y. ~ (?x. y = f x))    *)
      bspec_rule `\y. ?x. y = (f:'a->'b) x`
        (inst_type_rule [(`:'a`,`:'b`)] not_dist_forall_thm);
      (* |- (?y. ~ (?x. y = f x)) <=> (?y. !x. ~ (f x = y))  *)
      mk_exists_rule y
        (eq_trans_rule
          (bspec_rule `\x. y = (f:'a->'b) x` not_dist_exists_thm)
          (mk_forall_rule x (mk_not_rule (eq_sym_conv `y = (f:'a->'b) x`))) )
      ]);;

(* ind_suc_zero_exists_lemma : thm                                            *)
(*                                                                            *)
(*    |- ?(s:ind->ind) z. ONE_ONE s /\ (!i. ~(s i = z))                       *)

let ind_suc_zero_exists_lemma =
  let s = `s:ind->ind` and z = `z:ind` in
  let th1 = assume_rule `ONE_ONE (s:ind->ind) /\ ~ ONTO s` in
  (* |- ?s z. ONE_ONE s /\ (!i. ~(s i = z))           *)
  choose_rule (s,
    (* |- ?(f:ind->ind). ONE_ONE f /\ ~ ONTO f                       *)
    infinity_ax)
    (* ONE_ONE s /\ ~ ONTO s |- ?s z. ONE_ONE s /\ (!i. ~(s i = z))  *)
    (exists_rule (`?s z. ONE_ONE (s:ind->ind) /\ (!i. ~(s i = z))`, s)
      (* ONE_ONE s /\ ~ ONTO s |- ?z. ONE_ONE s /\ (!i. ~(s i = z))    *)
      (choose_rule (z,
        (* ONE_ONE s /\ ~ ONTO s |- ?z. !i. ~(s i = z)      *)
        eq_mp_rule
          (* |- ~ ONTO s <=> (?z. !i. ~(s i = z))             *)
          (spec_rule s
            (inst_type_rule [(a_ty,ind_ty);(b_ty,ind_ty)] not_onto_lemma) )
          (conjunct2_rule th1) )
        (* ONE_ONE s /\ ~ ONTO s, !i. ~(s i = z)            *)
        (*          |- ?z. ONE_ONE s /\ (!i. ~(s i = z))    *)
        (exists_rule (`?z. ONE_ONE (s:ind->ind) /\ (!i. ~(s i = z))`, z)
          (conj_rule
            (conjunct1_rule th1)
            (assume_rule `!i. ~((s:ind->ind) i = z)`) ))));;


(* Constants specification *)

let ind_suc_zero_spec =
  new_const_specification (["IND_SUC";"IND_ZERO"], ind_suc_zero_exists_lemma);;

let ind_zero_tm = `IND_ZERO`;;

let ind_suc_fn = `IND_SUC`;;


(* ind_suc_injective_thm : thm                                                *)
(*                                                                            *)
(*    |- !i j. IND_SUC i = IND_SUC j <=> i = j                                *)

let ind_suc_injective_thm = save_thm ("ind_suc_injective_thm",
  let i = `i:ind` and j = `j:ind` in
  (* |- !i j. IND_SUC i = IND_SUC j <=> i = j    *)
  list_gen_rule [i;j]
    (imp_antisym_rule
      (* |- IND_SUC i = IND_SUC j ==> i = j        *)
      (list_spec_rule [i;j]
        (eq_mp_rule
          (* |- ONE_ONE IND_SUC <=>                                *)
          (*        (!x1 x2. IND_SUC x1 = IND_SUC x2 ==> x1 = x2)  *)
          (app_beta_rhs_rule
            (inst_type_rule [(a_ty,ind_ty);(b_ty,ind_ty)] one_one_def)
            `IND_SUC` )
          (* |- ONE_ONE IND_SUC                                    *)
          (conjunct1_rule ind_suc_zero_spec) ))
      (* |- i = j ==> IND_SUC i = IND_SUC j        *)
      (disch_rule `(i:ind)=j`
        (mk_comb2_rule `IND_SUC`
          (assume_rule `(i:ind)=j`) )))
);;


(* ind_suc_not_zero_thm : thm                                                 *)
(*                                                                            *)
(*    |- !i. ~(IND_SUC i = IND_ZERO)                                          *)

let ind_suc_not_zero_thm = save_thm ("ind_suc_not_zero_thm",
  conjunct2_rule ind_suc_zero_spec
);;


end;;
