(* ========================================================================== *)
(* EQUALITY CONGRUENCE RULES (HOL Zero)                                       *)
(* - Derived equality congruence rules                                        *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2012                            *)
(* ========================================================================== *)


module EqCong : EqCong_sig = struct


(* This module implements equality congruence rules for equality, function    *)
(* application and predicate logic operators.  These are all trivial          *)
(* derivations of the primitive congruence rules 'mk_comb_rule' and           *)
(* 'mk_abs_rule' (see 'Thm' module) and the derived congruence rules          *)
(* 'mk_comb1_rule' and 'mk_comb2_rule' (see 'Equal' module).                  *)


open Equal;;



(* Utilities *)

let is_bool_eqthm th =
  try
    is_bool_term (eqthm_lhs th)
  with HolFail _ -> false;;



(* mk_bin_rule : term -> thm -> thm -> thm                                    *)
(*                                                                            *)
(* This is the equality congruence rule for binary function application.  It  *)
(* takes a binary function term and two equality theorems, and applies the    *)
(* function in curried form to corresponding sides of each theorem, under     *)
(* their unioned assumptions.  The type of the supplied function must be a    *)
(* binary curried function type, with first and second domain types equal to  *)
(* the type of each side of their corresponding theorems.                     *)
(*                                                                            *)
(*    `f`   A1 |- s1 = s2    A2 |- t1 = t2                                    *)
(*    ------------------------------------                                    *)
(*        A1 u A2 |- f s1 t1 = f s2 t2                                        *)


let mk_bin_rule f th1 th2 =
 try
  mk_comb_rule (mk_comb2_rule f th1) th2
 with HolFail _ ->
  let func = "mk_bin2_rule" in
  let (ty1,ty23) = try1 dest_fun_type (type_of f)
                                        (func,"Arg 1 not a binary function") in
  let (ty2,_) = try1 dest_fun_type ty23 (func,"Arg 1 not a binary function") in
  let tm1 = try1 eqthm_lhs th1        (func,"Arg 2 not an equality theorem") in
  let tm2 = try1 eqthm_lhs th2        (func,"Arg 3 not an equality theorem") in
  let () = assert1 (type_eq (type_of tm1) ty1)  (func,"LHS types not equal") in
  let () = assert1 (type_eq (type_of tm2) ty2)  (func,"RHS types not equal") in
  internal_error func;;


(* mk_bin1_rule : term -> thm -> term -> thm                                  *)
(*                                                                            *)
(* This is the equality congruence rule for binary function LHS application.  *)
(* It takes a binary function term, an equality theorem and a RHS argument    *)
(* term, and applies the function in curried form to corresponding sides of   *)
(* the theorem as its LHS argument and the supplied RHS argument.  The type   *)
(* of the supplied function must be a binary curried function type, with      *)
(* first domain type equal to the type of each side of the theorem, and       *)
(* second domain type equal to the type of the RHS argument term.             *)
(*                                                                            *)
(*    `f`   |- s1 = s2   `t`                                                  *)
(*    ----------------------                                                  *)
(*      |- f s1 t = f s2 t                                                    *)

let mk_bin1_rule f th1 tm2 =       (* |- s1 = s2     *)
 try
  mk_comb1_rule (mk_comb2_rule f th1) tm2       (* |- f s1 t = f s2 t      *)
 with HolFail _ ->
  let func = "mk_bin1_rule" in
  let (ty1,ty23) = try1 dest_fun_type (type_of f)
                                        (func,"Arg 1 not a binary function") in
  let (ty2,_) = try1 dest_fun_type ty23 (func,"Arg 1 not a binary function") in
  let tm1 = try1 eqthm_lhs th1        (func,"Arg 2 not an equality theorem") in
  let () = assert1 (type_eq (type_of tm1) ty1)  (func,"LHS types not equal") in
  let () = assert1 (type_eq (type_of tm2) ty2)  (func,"RHS types not equal") in
  internal_error func;;


(* mk_bin2_rule : term -> term -> thm -> thm                                  *)
(*                                                                            *)
(* This is the equality congruence rule for binary function RHS application.  *)
(* It takes a binary function term, a LHS argument term and an equality       *)
(* theorem, and applies the function in curried form to the supplied LHS      *)
(* argument and corresponding sides of the theorem as its RHS argument.  The  *)
(* type of the supplied function must be a binary curried function type, with *)
(* first domain type equal to the type of the LHS argument term, and second   *)
(* domain type equal to the type of each side of the theorem.                 *)
(*                                                                            *)
(*    `f`   `s`   |- t1 = t2                                                  *)
(*    ----------------------                                                  *)
(*      |- f s t1 = f s t2                                                    *)

let mk_bin2_rule f tm1 th2 =       (* |- t1 = t2     *)
 try
  mk_comb2_rule (mk_comb (f,tm1)) th2           (* |- f s t1 = f s t2      *)
 with HolFail _ ->
  let func = "mk_bin2_rule" in
  let (ty1,ty23) = try1 dest_fun_type (type_of f)
                                        (func,"Arg 1 not a binary function") in
  let (ty2,_) = try1 dest_fun_type ty23 (func,"Arg 1 not a binary function") in
  let tm2 = try1 eqthm_lhs th2        (func,"Arg 3 not an equality theorem") in
  let () = assert1 (type_eq (type_of tm1) ty1)  (func,"LHS types not equal") in
  let () = assert1 (type_eq (type_of tm2) ty2)  (func,"RHS types not equal") in
  internal_error func;;


(* mk_eq_rule : thm -> thm -> thm                                             *)
(*                                                                            *)
(* This is the equality congruence rule for equality.  It takes two equality  *)
(* theorems, and equates corresponding sides of the first theorem with the    *)
(* second, unioning the assumptions.  The types of each side of each equation *)
(* must all be equal.                                                         *)
(*                                                                            *)
(*    A1 |- s1 = s2    A2 |- t1 = t2                                          *)
(*    ------------------------------                                          *)
(*    A1 u A2 |- s1 = t1 <=> s2 = t2                                          *)

let mk_eq_rule tha thb =     (* A1 |- s1 = s2    A2 |- t1 = t2  *)
 try
  let f = (rator <* rator) (concl tha) in
  mk_bin_rule f tha thb              (* A1 u A2 |- s1 = t1 <=> s2 = t2  *)
 with HolFail _ ->
  let func = "mk_eq_rule" in
  let (tma,tmb) = (concl tha, concl thb) in
  let () = assert1 (is_eq tma)        (func,"Arg 1 not an equality theorem") in
  let () = assert1 (is_eq tmb)        (func,"Arg 2 not an equality theorem") in
  let () = assert1 (type_eq (type_of (eq_rhs tma)) (type_of (eq_rhs tmb)))
                                      (func,"Types not equal") in
  internal_error func;;


(* mk_eq1_rule : thm -> term -> thm                                           *)
(*                                                                            *)
(* This is the equality congruence rule for equality LHS.  It takes an        *)
(* equality theorem and a term, and equates each side of the theorem with the *)
(* supplied term.  The type of the supplied term must equal the types of each *)
(* side of the supplied theorem.                                              *)
(*                                                                            *)
(*      A |- s1 = s2   `t`                                                    *)
(*    ----------------------                                                  *)
(*    A |- s1 = t <=> s2 = t                                                  *)

let mk_eq1_rule tha tm =      (* A |- s1 = s2    t   *)
 try
  let f = (rator <* rator) (concl tha) in
  mk_bin1_rule f tha tm                    (* A |- s1 = t <=> s2 = t    *)
 with HolFail _ ->
  let func = "mk_eq1_rule" in
  let tma = concl tha in
  let () = assert1 (is_eq tma)        (func,"Arg 1 not an equality theorem") in
  let () = assert1 (same_types (eq_rhs tma) tm)     (func,"Types not equal") in
  internal_error func;;


(* mk_eq2_rule : term -> thm -> thm                                           *)
(*                                                                            *)
(* This is the equality congruence rule for equality RHS.  It takes a term    *)
(* and an equality theorem, and equates the term to each side of the theorem. *)
(* The type of the supplied term must equal the types of each side of the     *)
(* supplied theorem.                                                          *)
(*                                                                            *)
(*      `s`   A |- t1 = t2                                                    *)
(*    ----------------------                                                  *)
(*    A |- s = t1 <=> s = t2                                                  *)

let mk_eq2_rule tm thb =      (* s     A |- t1 = t2   *)
 try
  let f = (rator <* rator) (concl thb) in
  mk_bin2_rule f tm thb                    (* A |- s = t1 <=> s = t2    *)
 with HolFail _ ->
  let func = "mk_eq2_rule" in
  let tmb = concl thb in
  let () = assert1 (is_eq tmb)        (func,"Arg 2 not an equality theorem") in
  let () = assert1 (same_types (eq_rhs tmb) tm)     (func,"Types not equal") in
  internal_error func;;


(* mk_not_rule : thm -> thm                                                   *)
(*                                                                            *)
(* This is the equality congruence rule for logical negation.  Its takes a    *)
(* boolean equality theorem, and logically negates each side of the theorem.  *)
(*                                                                            *)
(*      A |- p1 <=> p2                                                        *)
(*    ------------------                                                      *)
(*    A |- ~ p1 <=> ~ p2                                                      *)

let not_fn = `$~`;;

let mk_not_rule th =      (* A1 |- p1 <=> p2   *)
 try
  mk_comb2_rule not_fn th                (* A |- ~ p1 <=> ~ p2    *)
 with HolFail _ ->
  let func = "mk_not_rule" in
  let () = assert1 (is_bool_eqthm th)    (func,"Not a bool equality thm") in
  internal_error func;;


(* mk_conj_rule : thm -> thm -> thm                                           *)
(*                                                                            *)
(* This is the equality congruence rule for conjunction.  It takes two        *)
(* boolean equality theorems, and conjoins corresponding sides of the first   *)
(* theorem with the second, unioning the assumptions.                         *)
(*                                                                            *)
(*    A1 |- p1 <=> p2    A2 |- q1 <=> q2                                      *)
(*    ----------------------------------                                      *)
(*     A1 u A2 |- p1 /\ q1 <=> p2 /\ q2                                       *)

let conj_fn = `$/\`;;

let mk_conj_rule tha thb =     (* A1 |- p1 <=> p2    A2 |- q1 <=> q2   *)
 try
  mk_bin_rule conj_fn tha thb      (* A1 u A2 |- p1 /\ q1 <=> p2 /\ q2    *)
 with HolFail _ ->
  let func = "mk_conj_rule" in
  let () = assert1 (is_bool_eqthm tha) (func,"Arg 1 not a bool equality thm") in
  let () = assert1 (is_bool_eqthm thb) (func,"Arg 2 not a bool equality thm") in
  internal_error func;;


(* mk_conj1_rule : thm -> term -> thm                                         *)
(*                                                                            *)
(* This is the equality congruence rule for conjunction LHS.  It takes a      *)
(* boolean equality theorem and a boolean term, and conjoins each side of the *)
(* theorem with the supplied term.                                            *)
(*                                                                            *)
(*      A |- p1 <=> p2   `q`                                                  *)
(*    ------------------------                                                *)
(*    A |- p1 /\ q <=> p2 /\ q                                                *)

let mk_conj1_rule tha tm =      (* A |- p1 <=> p2   *)
 try
  mk_bin1_rule conj_fn tha tm            (* A |- p1 /\ q <=> p2 /\ q    *)
 with HolFail _ ->
  let func = "mk_conj1_rule" in
  let () = assert1 (is_bool_eqthm tha) (func,"Arg 1 not a bool equality thm") in
  let () = assert1 (is_bool_term tm)   (func,"Arg 2 not boolean") in
  internal_error func;;


(* mk_conj2_rule : term -> thm -> thm                                         *)
(*                                                                            *)
(* This is the equality congruence rule for conjunction RHS.  It takes a      *)
(* boolean term and a boolean equality theorem, and conjoins the supplied     *)
(* term with each side of the theorem.                                        *)
(*                                                                            *)
(*      `p`   A |- q1 <=> q2                                                  *)
(*    ------------------------                                                *)
(*    A |- p /\ q1 <=> p /\ q2                                                *)

let mk_conj2_rule tm th =      (* A |- q1 <=> q2   *)
 try
  mk_bin2_rule conj_fn tm th             (* A |- p /\ q1 <=> p /\ q2    *)
 with HolFail _ ->
  let func = "mk_conj2_rule" in
  let () = assert1 (is_bool_term tm)  (func,"Arg 1 not boolean") in
  let () = assert1 (is_bool_eqthm th) (func,"Arg 2 not a bool equality thm") in
  internal_error func;;


(* mk_disj_rule : thm -> thm -> thm                                           *)
(*                                                                            *)
(* This is the equality congruence rule for disjunction.    It takes two      *)
(* boolean equality theorems, and disjoins corresponding sides of the first   *)
(* theorem with the second, unioning the assumptions.                         *)
(*                                                                            *)
(*    A1 |- p1 <=> p2    A2 |- q1 <=> q2                                      *)
(*    ----------------------------------                                      *)
(*     A1 u A2 |- p1 \/ q1 <=> p2 \/ q2                                       *)

let disj_fn = `$\/`;;

let mk_disj_rule tha thb =    (* A1 |- p1 <=> p2    A2 |- q1 <=> q2  *)
 try
  mk_bin_rule disj_fn tha thb       (* A1 u A2 |- p1 \/ q1 <=> p2 \/ q2    *)
 with HolFail _ ->
  let func = "mk_disj_rule" in
  let () = assert1 (is_bool_eqthm tha) (func,"Arg 1 not a bool equality thm") in
  let () = assert1 (is_bool_eqthm thb) (func,"Arg 2 not a bool equality thm") in
  internal_error func;;


(* mk_disj1_rule : thm -> term -> thm                                         *)
(*                                                                            *)
(* This is the equality congruence rule for disjunction LHS.  It takes a      *)
(* boolean equality theorem and a boolean term, and disjoins each side of the *)
(* theorem with the supplied term.                                            *)
(*                                                                            *)
(*      A |- p1 <=> p2   `q`                                                  *)
(*    ------------------------                                                *)
(*    A |- p1 \/ q <=> p2 \/ q                                                *)

let mk_disj1_rule th tm =          (* A |- p1 <=> p2     *)
 try
  mk_bin1_rule disj_fn th tm                (* A |- p1 \/ q <=> p2 \/ q  *)
 with HolFail _ ->
  let func = "mk_disj1_rule" in
  let () = assert1 (is_bool_eqthm th) (func,"Arg 1 not a bool equality thm") in
  let () = assert1 (is_bool_term tm)  (func,"Arg 2 not boolean") in
  internal_error func;;


(* mk_disj2_rule : term -> thm -> thm                                         *)
(*                                                                            *)
(* This is the equality congruence rule for disjunction RHS.  It takes a      *)
(* boolean term and a boolean equality theorem, and disjoins the supplied     *)
(* term with each side of the theorem.                                        *)
(*                                                                            *)
(*      `p`   A |- q1 <=> q2                                                  *)
(*    ------------------------                                                *)
(*    A |- p \/ q1 <=> p \/ q2                                                *)

let mk_disj2_rule tm th =      (* A |- q1 <=> q2   *)
 try
  mk_bin2_rule disj_fn tm th                (* A |- p \/ q1 <=> p \/ q2   *)
 with HolFail _ ->
  let func = "mk_disj2_rule" in
  let () = assert1 (is_bool_term tm)   (func,"Arg 1 not boolean") in
  let () = assert1 (is_bool_eqthm th)  (func,"Arg 2 not a bool equality thm") in
  internal_error func;;


(* mk_imp_rule : thm -> thm -> thm                                            *)
(*                                                                            *)
(* This is the equality congruence rule for implication.  It takes two        *)
(* boolean equality theorems, and creates implications out of corresponding   *)
(* sides of the first theorem and the second, unioning the assumptions.       *)
(*                                                                            *)
(*    A1 |- p1 <=> p2    A2 |- q1 <=> q2                                      *)
(*    ----------------------------------                                      *)
(*    A1 u A2 |- p1 ==> q1 <=> p2 ==> q2                                      *)

let imp_fn = `$==>`;;

let mk_imp_rule tha thb =    (* A1 |- p1 <=> p2    A2 |- q1 <=> q2  *)
 try
  mk_bin_rule imp_fn tha thb     (* A1 u A2 |- p1 ==> q1 <=> p2 ==> q2    *)
 with HolFail _ ->
  let func = "mk_imp_rule" in
  let () = assert1 (is_bool_eqthm tha) (func,"Arg 1 not a bool equality thm") in
  let () = assert1 (is_bool_eqthm thb) (func,"Arg 2 not a bool equality thm") in
  internal_error func;;


(* mk_imp1_rule : thm -> term -> thm                                          *)
(*                                                                            *)
(* This is the equality congruence rule for implication LHS.  It takes a      *)
(* boolean equality theorem and a boolean term, and creates implications out  *)
(* of each side of the theorem, with the theorem side as the antecedent and   *)
(* the term as the consequent.                                                *)
(*                                                                            *)
(*       A |- p1 <=> p2   `q`                                                 *)
(*    --------------------------                                              *)
(*    A |- p1 ==> q <=> p2 ==> q                                              *)

let mk_imp1_rule th tm =      (* A |- p1 <=> p2   *)
 try
  mk_bin1_rule imp_fn th tm             (* A |- p1 ==> q <=> p2 ==> q   *)
 with HolFail _ ->
  let func = "mk_imp1_rule" in
  let () = assert1 (is_bool_eqthm th)  (func,"Arg 1 not a bool equality thm") in
  let () = assert1 (is_bool_term tm)   (func,"Arg 2 not boolean") in
  internal_error func;;


(* mk_imp2_rule : term -> thm -> thm                                          *)
(*                                                                            *)
(* This is the equality congruence rule for implication RHS.  It takes a      *)
(* boolean term and a boolean equality theorem, and makes the term an         *)
(* antecedent of each side of the theorem.                                    *)
(*                                                                            *)
(*      `p`   A |- q1 <=> q2                                                  *)
(*    --------------------------                                              *)
(*    A |- p ==> q1 <=> p ==> q2                                              *)

let mk_imp2_rule tm th =    (* A |- q1 <=> q2   *)
 try
  mk_bin2_rule imp_fn tm th             (* A |- p ==> q1 <=> p ==> q2    *)
 with HolFail _ ->
  let func = "mk_imp2_rule" in
  let () = assert1 (is_bool_term tm)   (func,"Arg 1 not a boolean") in
  let () = assert1 (is_bool_eqthm th)  (func,"Arg 2 not a bool equality thm") in
  internal_error func;;


(* mk_forall_rule : term -> thm -> thm                                        *)
(*                                                                            *)
(* This is the equality congruence rule for universal quantification.  It     *)
(* takes a variable and an equality theorem, and universally quantifies the   *)
(* variable on both sides of the theorem.  The variable must not occur free   *)
(* in the assumptions of the supplied theorem.                                *)
(*                                                                            *)
(*       `x`   A |- p1 <=> p2         [ "x" not free in `A` ]                 *)
(*    --------------------------                                              *)
(*    A |- (!x. p1) <=> (!x. p2)                                              *)

let mk_forall_rule v th =      (* A |- p1 <=> p2   *)
 try
  let forall_fn = mk_iconst ("!", [(a_ty, type_of v)]) in
  let th1 = mk_abs_rule v th in       (* A |- (\x. p1) <=> (\x. p2)    *)
  mk_comb2_rule forall_fn th1         (* A |- (!x. p1) <=> (!x. p2)    *)
 with HolFail _ ->
  let func = "mk_forall_rule" in
  let () = assert1 (is_var v)          (func,"Arg 1 not a variable") in
  let () = assert1 (is_bool_eqthm th)  (func,"Arg 2 not a bool equality thm") in
  let () = assert1 (not (exists (var_free_in v) (asms th)))
                       (func,"Supplied variable occurs free in assumptions") in
  internal_error func;;


(* mk_exists_rule : term -> thm -> thm                                        *)
(*                                                                            *)
(* This is the equality congruence rule for existential quantification.  It   *)
(* takes a variable and an equality theorem, and existentially quantifies the *)
(* variable on both sides of the theorem.  The variable must not occur free   *)
(* in the assumptions of the supplied theorem.                                *)
(*                                                                            *)
(*       `x`   A |- p1 <=> p2         [ "x" not free in `A` ]                 *)
(*    --------------------------                                              *)
(*    A |- (?x. p1) <=> (?x. p2)                                              *)

let mk_exists_rule v th  =      (* A |- p1 <=> p2   *)
 try
  let exists_fn = mk_iconst ("?", [(a_ty, type_of v)]) in
  let th1 = mk_abs_rule v th in       (* A |- (\x. p1) <=> (\x. p2)    *)
  mk_comb2_rule exists_fn th1         (* A |- (?x. p1) <=> (?x. p2)    *)
 with HolFail _ ->
  let func = "mk_exists_rule" in
  let () = assert1 (is_var v)          (func,"Arg 1 not a variable") in
  let () = assert1 (is_bool_eqthm th)  (func,"Arg 2 not a bool equality thm") in
  let () = assert1 (not (exists (var_free_in v) (asms th)))
                       (func,"Supplied variable occurs free in assumptions") in
  internal_error func;;


(* mk_uexists_rule : term -> thm -> thm                                       *)
(*                                                                            *)
(* This is the equality congruence rule for unique existential                *)
(* quantification.  It takes a variable and an equality theorem, and unique-  *)
(* existentially quantifies the variable on both sides of the theorem.  The   *)
(* variable must not occur free in the assumptions of the supplied theorem.   *)
(*                                                                            *)
(*        `x`   A |- p1 <=> p2        [ "x" not free in `A` ]                 *)
(*    ----------------------------                                            *)
(*    A |- (?!x. p1) <=> (?!x. p2)                                            *)

let mk_uexists_rule v th  =      (* A |- p1 <=> p2   *)
 try
  let uexists_fn = mk_iconst ("?!", [(a_ty, type_of v)]) in
  let th1 = mk_abs_rule v th in       (* A |- (\x. p1) <=> (\x. p2)    *)
  mk_comb2_rule uexists_fn th1         (* A |- (?!x. p1) <=> (?!x. p2)  *)
 with HolFail _ ->
  let func = "mk_uexists_rule" in
  let () = assert1 (is_var v)          (func,"Arg 1 not a variable") in
  let () = assert1 (is_bool_eqthm th)  (func,"Arg 2 not a bool equality thm") in
  let () = assert1 (not (exists (var_free_in v) (asms th)))
                       (func,"Supplied variable occurs free in assumptions") in
  internal_error func;;


(* mk_select_rule : term -> thm -> thm                                        *)
(*                                                                            *)
(* This is the equality congruence rule for selection.  It takes a variable   *)
(* and an equality theorem, and selects the variable from both sides of the   *)
(* theorem.  The variable must not occur free in the assumptions of the       *)
(* supplied theorem.                                                          *)
(*                                                                            *)
(*      `x`   A |- p1 <=> p2        [ "x" not free in `A` ]                   *)
(*    ------------------------                                                *)
(*    A |- (@x. p1) = (@x. p2)                                                *)

let mk_select_rule v th  =      (* A |- p1 = p2   *)
 try
  let select_fn = mk_iconst ("@", [(a_ty, type_of v)]) in
  let th1 = mk_abs_rule v th in         (* A |- (\x. p1) = (\x. p2)    *)
  mk_comb2_rule select_fn th1           (* A |- (@x. p1) = (@x. p2)    *)
 with HolFail _ ->
  let func = "mk_select_rule" in
  let () = assert1 (is_var v)          (func,"Arg 1 not a variable") in
  let () = assert1 (is_bool_eqthm th)  (func,"Arg 2 not a bool equality thm") in
  let () = assert1 (not (exists (var_free_in v) (asms th)))
                       (func,"Supplied variable occurs free in assumptions") in
  internal_error func;;


end;;
