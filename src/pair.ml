(* ========================================================================== *)
(* PAIRS (HOL Zero)                                                           *)
(* - Theory defining ordered pairs, plus basic derived properties             *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2009-2015                            *)
(* ========================================================================== *)


module Pair : Pair_sig = struct


(* This module extends the HOL logic with the theory of ordered pairs.  This  *)
(* involves giving theory entity definitions for the product type operator,   *)
(* the pairing function and the constants "FST" and "SND", and proving a few  *)
(* basic properties.  Syntax functions and equality congruence rules are also *)
(* provided.                                                                  *)


open Def1;;

open Equal;;
open EqCong;;
open Bool;;
open BoolClass;;



(* ** THE PRODUCT TYPE ** *)

(* Firstly a HOL type operator for pairs, called "#" and referred to as "the  *)
(* product type", is defined.  This is done using the type of boolean-valued  *)
(* binary functions as the representation type.                               *)


(* Supporting definition *)

(* The "MkPairRep" function returns the concrete representation for a given   *)
(* pair's two components (i.e. the representation in terms of existing types, *)
(* before the product type is defined).  This representation is a function    *)
(* that takes two arguments and returns `true` for just one combination of    *)
(* its arguments - when each argument is equal to its respective pair         *)
(* component.  This is used to define both "IsPairRep" and the pairing        *)
(* function.                                                                  *)

let mk_pair_rep_def =
  new_const_definition `MkPairRep = \(x:'a) (y:'b). \a b. a = x /\ b = y`;;


(* Characteristic function *)

(* "IsPairRep" is the characteristic function for the product type operator.  *)
(* It takes a boolean-valued binary function and returns whether there is a   *)
(* pair for which this is the concrete representation.                        *)

let is_pair_rep_def =
  new_const_definition
       `IsPairRep = \(r:'a->'b->bool). ?a b. r = MkPairRep a b`;;


(* mk_pair_rep_lemma                                                          *)
(*                                                                            *)
(*    |- !c d. ?a b. MkPairRep c d = MkPairRep a b                            *)

let mk_pair_rep_lemma =
  let c = `c:'a` and d = `d:'b` in
  (* |- !c d. ?a b. MkPairRep c d = MkPairRep a b   *)
  list_gen_rule [c;d]
    (exists_rule (`?(a:'a) (b:'b). MkPairRep c d = MkPairRep a b`, c)
      (exists_rule (`?b. MkPairRep (c:'a) (d:'b) = MkPairRep c b`, d)
        (eq_refl_conv `MkPairRep (c:'a) (d:'b)`) ));;


(* pair_rep_exists_lemma                                                      *)
(*                                                                            *)
(*    |- ?r. IsPairRep r                                                      *)
(*                                                                            *)
(* This theorem shows that the characteristic function prescribes a non-empty *)
(* subset, and is the theorem supplied in the definition of the product type. *)

let pair_rep_exists_lemma =
  let c = `c:'a` and d = `d:'b` and r = `r : 'a->'b->bool` in
  (* |- ?r. IsPairRep r                                    *)
  eq_mp_rule
    (* |- (?r a b. r = MkPairRep a b) <=> (?r. IsPairRep r)  *)
    (mk_exists_rule r
      (eq_sym_rule
        (* |- IsPairRep r <=> (?a b. r = MkPairRep a b)          *)
        (app_beta_rhs_rule is_pair_rep_def r) ))
    (* |- ?r a b. r = MkPairRep a b                          *)
    (exists_rule
              (`?r (a:'a) (b:'b). r = MkPairRep a b`, `MkPairRep (c:'a) (d:'b)`)
      (* |- ?a b. MkPairRep c d = MkPairRep a b                *)
      (list_spec_rule [c;d] mk_pair_rep_lemma) );;


(* Product type definition *)

(* The product type can now be defined.                                       *)

let _ = set_type_fixity ("#", Infix (10,RightAssoc));;

let prod_def = new_tyconst_definition ("#", pair_rep_exists_lemma);;


(* Product type bijections *)

let (prod_bij_def1,prod_bij_def2) =
  new_type_bijections "#" ("PairAbs","PairRep");;
               (* |- !a. PairAbs (PairRep a) = a                   *)
               (* |- !r. IsPairRep r <=> PairRep (PairAbs r) = r   *)


(* Type syntax functions *)

let mk_prod_type (ty1,ty2) = mk_comp_type ("#",[ty1;ty2]);;

let list_mk_prod_type tys = foldr1' mk_prod_type tys;;

let dest_prod_type ty =
  match (dest_type ty) with
    Type_comp ("#",[ty1;ty2])
        -> (ty1,ty2)
  | _   -> hol_fail ("dest_prod_type","Not a product type");;

let strip_prod_type ty = unfoldr1 dest_prod_type ty;;

let is_prod_type ty = can dest_prod_type ty;;



(* ** PAIRS ** *)

(* The pairing function, that constructs a pair expression from two           *)
(* components, can now be defined.  A few basic properties about pairs are    *)
(* also proved.                                                               *)


(* Pair definition *)

(* The pairing function, called "PAIR", takes two arguments and returns the   *)
(* corresponding element in the product type.  It is simply defined as the    *)
(* product type's abstraction of the "MkPairRep" function.  It has special    *)
(* support in the parser/printer, so that the quotation `(t1,t2)` is parsed/  *)
(* printed for the internal term `PAIR t1 t2`.                                *)

let pair_def =
  new_const_definition `PAIR = \(x:'a) (y:'b). PairAbs (MkPairRep x y)`;;


(* Pair syntax functions *)

let mk_pair (tm1,tm2) =
  let ty1 = type_of tm1  and ty2 = type_of tm2 in
  let f = mk_iconst ("PAIR", [(a_ty,ty1);(b_ty,ty2)]) in
  mk_bin (f,tm1,tm2);;

let list_mk_pair tms = try2  (foldr1' mk_pair) tms    "list_mk_pair";;

let dest_pair tm =
  try1 (dest_cbin "PAIR") tm        ("dest_pair","Not a pair expression");;

let strip_pair tm = unfoldr1 dest_pair tm;;

let flatstrip_pair tm = unfold dest_pair tm;;

let is_pair tm = can dest_pair tm;;


(* mk_pair_rule : thm -> thm -> thm                                           *)
(*                                                                            *)
(* This is the equality congruence rule for pairing.  It takes two equality   *)
(* theorems, and pairs corresponding sides of the first theorem with the      *)
(* second, unioning the assumptions.                                          *)
(*                                                                            *)
(*    A1 |- x1 = x2    A2 |- y1 = y2                                          *)
(*    ------------------------------                                          *)
(*     A1 u A2 |- (x1,y1) = (x2,y2)                                           *)

let mk_pair_rule th1 th2 =
 try
  let ty1 = type_of (eqthm_rhs th1)  and ty2 = type_of (eqthm_rhs th2)  in
  let f = mk_iconst ("PAIR",[(a_ty,ty1);(b_ty,ty2)]) in
  mk_bin_rule f th1 th2
 with HolFail _ ->
  let func = "mk_pair_rule" in
  let () = assert1 (is_eqthm th1)       (func,"Arg 1 not an equality") in
  let () = assert1 (is_eqthm th2)       (func,"Arg 2 not an equality") in
  internal_error func;;


(* mk_pair1_rule : thm -> term -> thm                                         *)
(*                                                                            *)
(* This is the equality congruence rule for pair LHS.  It takes an equality   *)
(* theorem and a term, and pairs each side of the theorem with the term.      *)
(*                                                                            *)
(*     A |- x1 = x2   `y`                                                     *)
(*    --------------------                                                    *)
(*    A |- (x1,y) = (x2,y)                                                    *)

let mk_pair1_rule th1 tm =
 try
  let ty1 = type_of (eqthm_rhs th1)  and ty2 = type_of tm  in
  let f = mk_iconst ("PAIR",[(a_ty,ty1);(b_ty,ty2)]) in
  mk_bin1_rule f th1 tm
 with HolFail _ ->
  let func = "mk_pair1_rule" in
  let () = assert1 (is_eqthm th1)       (func,"Arg 1 not an equality") in
  internal_error func;;


(* mk_pair2_rule : term -> thm -> thm                                         *)
(*                                                                            *)
(* This is the equality congruence rule for pair RHS.  It takes a term and an *)
(* equality theorem, and pairs the term with each side of the theorem.        *)
(*                                                                            *)
(*     `x`   A |- y1 = y2                                                     *)
(*    --------------------                                                    *)
(*    A |- (x,y1) = (x,y2)                                                    *)

let mk_pair2_rule tm th2 =
 try
  let ty1 = type_of tm  and ty2 = type_of (eqthm_rhs th2)  in
  let f = mk_iconst ("PAIR",[(a_ty,ty1);(b_ty,ty2)]) in
  mk_bin2_rule f tm th2
 with HolFail _ ->
  let func = "mk_pair2_rule" in
  let () = assert1 (is_eqthm th2)       (func,"Arg 2 not an equality") in
  internal_error func;;


(* rep_abs_pair_lemma                                                         *)
(*                                                                            *)
(*    |- !x y. PairRep (PairAbs (MkPairRep x y)) = MkPairRep x y              *)

let rep_abs_pair_lemma =
  let x = `x:'a` and y = `y:'b` in
  let r = `MkPairRep (x:'a) (y:'b)` in
  (* |- !x y. PairRep (PairAbs (MkPairRep x y)) = MkPairRep x y  *)
  list_gen_rule [x;y]
    (eq_mp_rule
      (eq_trans_rule
        (* |- (?a b. MkPairRep x y = MkPairRep a b) <=>           *)
        (*                            IsPairRep (MkPairRep x y)   *)
        (eq_sym_rule (app_beta_rhs_rule is_pair_rep_def r))
        (* |- IsPairRep (MkPairRep x y) <=>                       *)
        (*     PairRep (PairAbs (MkPairRep x y)) = MkPairRep x y  *)
        (spec_rule r prod_bij_def2) )
      (* |- ?a b. MkPairRep x y = MkPairRep a b                 *)
      (list_spec_rule [x;y] mk_pair_rep_lemma) );;


(* pair_eq_thm                                                                *)
(*                                                                            *)
(*    |- !x y u v. (x,y) = (u,v) <=> x = u /\ y = v                           *)

let pair_eq_thm = save_thm ("pair_eq_thm",
  let x = `x:'a` and y = `y:'b` in
  let u = `u:'a` and v = `v:'b` in
  let repfn = mk_gconst "PairRep" in
  let th1 = assume_rule `(x:'a)=u /\ (y:'b)=v` in
                                     (* x = u /\ y = v |- x = u /\ y = v    *)
  (* |- !x y u v. (x,y) = (u,v) <=> x = u /\ y = v       *)
  list_gen_rule [x;y;u;v]
    (deduct_antisym_rule
      (* x = u /\ y = v |- (x,y) = (u,v)                     *)
      (mk_pair_rule (conjunct1_rule th1) (conjunct2_rule th1))
      (* (x,y) = (u,v) |- x = u /\ y = v                     *)
      (eq_mp_rule
        (* (x,y) = (u,v) |- x = x /\ y = y <=> x = u /\ y = v  *)
        (list_app_beta_rule
          (* (x,y) = (u,v) |- (\a b. a=x /\ b=y) = (\a b. a=u /\ b=v)   *)
          (list_eq_trans_rule [
            (* |- (\a b. a=x /\ b=y) = MkPairRep x y                      *)
            eq_sym_rule (list_app_beta_rhs_rule mk_pair_rep_def [x;y]);
            (* |- ...                = PairRep (PairAbs (MkPairRep x y))  *)
            eq_sym_rule (list_spec_rule [x;y] rep_abs_pair_lemma);
            (* (x,y) = (u,v) |- ...  = PairRep (PairAbs (MkPairRep u v))  *)
            mk_comb2_rule repfn
              (eq_mp_rule
                (mk_eq_rule
                  (list_app_beta_rhs_rule pair_def [x;y])
                  (list_app_beta_rhs_rule pair_def [u;v]) )
                (assume_rule `((x:'a),(y:'b))=(u,v)`) );
            (* |- ...                = MkPairRep u v                      *)
            list_spec_rule [u;v] rep_abs_pair_lemma;
            (* |- ...                = (\a b. a = u /\ b = v)             *)
            list_app_beta_rhs_rule mk_pair_rep_def [u;v]
            ])
          [x;y] )
        (* |- x = x /\ y = y                                   *)
        (conj_rule (eq_refl_conv x) (eq_refl_conv y)) ))
);;


(* pair_surjective_thm                                                        *)
(*                                                                            *)
(*    |- !p. ?x y. p = (x,y)                                                  *)

let pair_surjective_thm = save_thm ("pair_surjective_thm",
  let a = `a:'a` and b = `b:'b` and p = `p:'a#'b` in
  let absfn = mk_gconst "PairAbs" and repfn = mk_gconst "PairRep" in
  let th1 = spec_rule p prod_bij_def1 in     (* |- PairAbs (PairRep p) = p  *)
  (* |- !p. ?x y. p = (x,y)             *)
  gen_rule p
    (prove_asm_rule
      (* |- ?a b. PairRep p = MkPairRep a b                   *)
      (eq_mp_rule
        (eq_trans_rule
          (* |- PairRep (PairAbs (PairRep p)) = PairRep p         *)
          (*      <=> IsPairRep (PairRep p)                       *)
          (eq_sym_rule
            (spec_rule `PairRep (p:'a#'b)` prod_bij_def2) )
          (* |- IsPairRep (PairRep p) <=> (?a b. PairRep p = MkPairRep a b)  *)
          (app_beta_rhs_rule is_pair_rep_def `PairRep (p:'a#'b)`) )
        (* |- PairRep (PairAbs (PairRep p)) = PairRep p    *)
        (mk_comb2_rule repfn th1) )
      (* ?a b. PairRep p = MkPairRep a b |- ?x y. p = (x,y)   *)
      (choose_rule (a, assume_rule `?a b. PairRep (p:'a#'b) = MkPairRep a b`)
        (choose_rule (b, assume_rule `?b. PairRep (p:'a#'b) = MkPairRep a b`)
          (* PairRep p = MkPairRep a b |- ?x y. p = (x,y)         *)
          (exists_rule (`?x y. (p:'a#'b) = (x,y)`, a)
            (exists_rule (`?y. (p:'a#'b) = (a,y)`, b)
              (* PairRep p = MkPairRep a b |- p = (a,b)               *)
              (list_eq_trans_rule [
                (* |- p = PairAbs (PairRep p)                           *)
                eq_sym_rule th1;
                (* PairRep p = MkPairRep a b                            *)
                (*    |- PairAbs (PairRep p) = PairAbs (MkPairRep a b)  *)
                mk_comb2_rule absfn
                  (assume_rule `PairRep (p:'a#'b) = MkPairRep a b`);
                (* |- PairAbs (MkPairRep a b) = (a,b)                   *)
                eq_sym_rule (list_app_beta_rhs_rule pair_def [a;b])
                ] ))))))
);;



(* ** FST AND SND ** *)

(* The functions "FST" and "SND" are now defined for selecting respectively   *)
(* the first and second components of a pair.                                 *)


(* Definitions *)

let fst_def = new_const_definition `FST = \(p:'a#'b). @x. ?y. p = (x,y)`;;

let snd_def = new_const_definition `SND = \(p:'a#'b). @y. ?x. p = (x,y)`;;


(* fst_thm                                                                    *)
(*                                                                            *)
(*    |- !x y. FST (x,y) = x                                                  *)

let fst_thm = save_thm ("fst_thm",
  let x = `x:'a` and y = `y:'b` in
  let u = `u:'a` and v = `v:'b` in
  (* |- !x y . FST (x,y) = x                                *)
  list_gen_rule [x;y]
    (list_eq_trans_rule [
      (* |- FST (x,y) = (@x'. ?y'. (x,y) = (x',y'))             *)
      app_beta_rhs_rule fst_def `((x:'a),(y:'b))`;
      (* |- (@u. ?v. (x,y) = (u,v)) = (@u. ?v. x=u /\ y=v)      *)
      mk_select_rule u
        (mk_exists_rule v
          (* |- (x,y) = (u,v) <=> x=u /\ y=v                        *)
          (list_spec_rule [x;y;u;v] pair_eq_thm) );
      (* |- (@u. ?v. x=u /\ y=v) = x                            *)
      eq_sym_rule
        (* |- x = (@u. ?v. x=u /\ y=v)                            *)
        (choose_rule (v,
          (* |- ?v. x = (@u. ?v. x=u /\ y=v) /\ y = v               *)
          select_rule
            (* |- ?u v. x=u /\ y=v                                    *)
            (exists_rule (`?(u:'a) (v:'b). x = u /\ y = v`, x)
              (exists_rule (`?(v:'b). x = (x:'a) /\ y = v`, y)
                (* |- x = x /\ y = y                                       *)
                (conj_rule (eq_refl_conv x) (eq_refl_conv y)) )) )
          (* x = (@u. ?v. x=u /\ y=v) /\ y = v |- x = (@u. ?v. x=u /\ y=v) *)
          (conjunct1_rule
            (assume_rule `x = (@(u:'a). ?(v:'b). x=u /\ y=v) /\ y = v`) ))
      ] )
);;


(* snd_thm                                                                    *)
(*                                                                            *)
(*    |- !x y. SND (x,y) = y                                                  *)

let snd_thm = save_thm ("snd_thm",
  let x = `x:'a` and y = `y:'b` in
  let u = `u:'a` and v = `v:'b` in
  list_gen_rule [x;y]
   (list_eq_trans_rule [
     (* |- SND (x,y) = (@y'. ?x'. (x,y) = (x',y'))        *)
     app_beta_rhs_rule snd_def `((x:'a),(y:'b))`;
     (* |- (@v. ?u. (x,y) = (u,v)) = (@v. ?u. x=u /\ y=v) *)
     mk_select_rule v
       (mk_exists_rule u
         (* |- (x,y) = (u,v) <=> x = u /\ y = v               *)
         (list_spec_rule [x;y;u;v] pair_eq_thm) );
     (* |- (@v. ?u. x = u /\ y = v) = y                   *)
     eq_sym_rule
       (* |- y = (@v. ?u. x=u /\ y=v)                       *)
       (choose_rule (u,
         (* |- ?u. x = u /\ y = (@v. ?u. x=u /\ y=v)          *)
         (select_rule
           (* |- ?v u. x=u /\ y=v                               *)
           (exists_rule (`?(v:'b) (u:'a). x = u /\ y = v`, y)
             (exists_rule (`?(u:'a). x = u /\ (y:'b) = y`, x)
               (* |- x=x /\ y=y                                     *)
               (conj_rule (eq_refl_conv x) (eq_refl_conv y)) ))) )
         (* x = u /\ y = (@v. ?u. x=u /\ y=v) |- y = (@v. ?u. x=u /\ y=v)  *)
         (conjunct2_rule
           (assume_rule `x = u /\ y = (@(v:'b). ?(u:'a). x=u /\ y=v)`) ))
     ] )
);;


(* fst_snd_thm                                                                *)
(*                                                                            *)
(*    |- !p. (FST p, SND p) = p                                               *)

let fst_snd_thm = save_thm ("fst_snd_thm",
  let x = `x:'a` and y = `y:'b` and p = `p:'a#'b`  in
  gen_rule p
    (prove_asm_rule
      (spec_rule p pair_surjective_thm)
      (* ?x y. p = (x,y) |- (FST p, SND p) = p         *)
      (choose_rule (x,
         assume_rule `?x y. (p:'a#'b) = (x,y)`)
        (choose_rule (y,
           assume_rule `?y. (p:'a#'b) = (x,y)`)
          (* p = (x,y) |- (FST p, SND p) = p               *)
          (subs_rule
            (* p = (x,y) |- (x,y) = p                        *)
            [eq_sym_rule (assume_rule `(p:'a#'b) = (x,y)`)]
            (* |- (FST (x,y), SND (x,y)) = (x,y)             *)
            (mk_pair_rule
              (list_spec_rule [x;y] fst_thm)
              (list_spec_rule [x;y] snd_thm) )))))
);;


end;;
