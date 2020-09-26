(* ========================================================================== *)
(* BOOLEANS (HOL Zero)                                                        *)
(* - Extra theory and derived inference rules for predicate logic             *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2015                            *)
(* ========================================================================== *)


module Bool : Bool_sig = struct


(* This module extends the boolean-related theory by giving definitions for   *)
(* classic predicate logic theory entities not introduced in 'CoreThry', and  *)
(* adds various derived syntax functions, theorems and inference rules.  Note *)
(* that derivations relying on the Axiom of Choice are separated out into the *)
(* 'BoolClass' module.                                                        *)


open Equal;;


(* Utilities *)

let is_bool_eqthm th =
  try
    is_bool_term (eqthm_lhs th)
  with HolFail _ -> false;;


(* HOL variables *)

let p = `p:bool`;;
let q = `q:bool`;;
let r = `r:bool`;;

let p_ = `p_:bool`;;
let p1_ = `p1_:bool`;;
let p2_ = `p2_:bool`;;



(* ** NEW CONSTANTS ** *)


(* Falsity *)

let false_def =
  new_const_definition `false = (!(p:bool). p)`;;

let false_tm = `false`;;


(* Disjunction *)

let _ = set_fixity ("\\/", Infix (15,RightAssoc));;

let disj_def =
  new_const_definition `$\/ = (\p1 p2. !p. (p1 ==> p) ==> (p2 ==> p) ==> p)`;;

let mk_disj (tm1,tm2) =
  let func = "mk_disj" in
  let () = assert1 (is_bool_term tm1)     (func,"Arg 1 not boolean") in
  let () = assert1 (is_bool_term tm2)     (func,"Arg 2 not boolean") in
  let f = mk_gconst "\\/" in
  mk_bin (f,tm1,tm2);;

let list_mk_disj tms = try2 (foldr1' mk_disj) tms    "list_mk_disj";;

let dest_disj tm = try1 (dest_cbin "\\/") tm ("dest_disj","Not a disjunction");;

let strip_disj tm = unfoldr1 dest_disj tm;;

let flatstrip_disj tm = unfold dest_disj tm;;

let is_disj tm = is_cbin "\\/" tm;;


(* Logical negation *)

let _ = set_fixity ("~", Prefix);;

let not_def =
  new_const_definition `$~ = (\p. p ==> false)`;;

let mk_not tm0 =
  let () = assert1 (is_bool_term tm0)     ("mk_not","Not a boolean") in
  let f = mk_gconst "~" in
  mk_comb (f,tm0);;

let dest_not tm =
 try
  let (f,tm0) = dest_comb tm in
  let () = assert0 (const_name f = "~")         LocalFail in
  tm0
 with LocalFail | HolFail _ -> hol_fail ("dest_not","Not a negation");;

let is_not tm = can dest_not tm;;


(* Unique existential quantification *)

let _ = set_fixity ("?!", Binder);;

let uexists_def =
  new_const_definition `$?! = (\(P:'a->bool). ?x. P x /\ (!y. P y ==> y = x))`;;

let mk_uexists (v,tm0) =
  let func = "mk_uexists" in
  let () = assert1 (is_bool_term tm0)      (func,"Arg 2 not boolean") in
  let f = mk_iconst ("?!", [(a_ty, type_of v)]) in
  try2 mk_binder (f,v,tm0)                func;;

let dest_uexists tm =
  try1 (dest_cbinder "?!") tm    ("dest_uexists","Not a unique-existential");;

let is_uexists tm = is_cbinder "?!" tm;;


(* Conditional *)

(* The internal constant for conditional expressions is called "COND".  It    *)
(* has special support in the parser/printer, so that                         *)
(*    `if c then t1 else t2`                                                  *)
(* is parsed/printed for the internal term                                    *)
(*    `COND c t1 t2`.                                                         *)

let cond_def =
  new_const_definition
    `COND =
        (\p (t1:'a) t2. @x. (p = true ==> x = t1) /\ (p = false ==> x = t2))`;;

let mk_cond (tm1,tm2,tm3) =
  let func = "mk_cond" in
  let ty2 = type_of tm2  and ty3 = type_of tm3 in
  let () = assert1 (is_bool_term tm1)      (func,"Arg 1 not boolean") in
  let () = assert1 (type_eq ty2 ty3)
                                 (func,"Arg 2 type not equal to Arg 3 type") in
  let f = mk_iconst ("COND", [(a_ty,ty2)]) in
  list_mk_comb (f, [tm1;tm2;tm3]);;

let dest_cond tm =
 try
  let (f,tms) = strip_comb tm in
  let () = assert0 (const_name f = "COND")     LocalFail in
  match tms with
    [tm1;tm2;tm3] -> (tm1,tm2,tm3)
  | _             -> raise LocalFail
 with LocalFail | HolFail _ ->
                       hol_fail ("dest_cond","Not a conditional expression");;

let is_cond tm = can dest_cond tm;;



(* ** DERIVED INFERENCE RULES ** *)

(* This section derives various classic predicate logic inference rules.  It  *)
(* starts by proving an important property: that "true" holds.                *)


(* truth_thm : thm                                                            *)
(*                                                                            *)
(*    |- true                                                                 *)

let truth_thm = save_thm ("truth_thm",
  (* |- true                        *)
  eq_mp_rule
    (* |- (\p. p) = (\p. p) <=> true  *)
    (eq_sym_rule true_def)
    (* |- (\p. p) = (\p. p)           *)
    (eq_refl_conv `\(p:bool).p`)
);;


(* eqt_elim_rule : thm -> thm                                                 *)
(*                                                                            *)
(* This is the truth equivalence elimination rule.  It takes an equality      *)
(* theorem that has truth on the RHS, and returns a theorem stating that the  *)
(* LHS holds, under the same assumptions.                                     *)
(*                                                                            *)
(*    A |- p <=> true                                                         *)
(*    ---------------                                                         *)
(*        A |- p                                                              *)

let eqt_elim_rule th =            (* A |- p <=> true    *)
 try
  eq_mp_rule (eq_sym_rule th) truth_thm     (* A |- p                *)
 with HolFail _ ->
  let func = "eqt_elim_rule" in
  let tm2 = try1 eqthm_rhs th              (func,"Not an equality theorem") in
  let () = assert1 (term_eq tm2 true_tm)   (func,"Theorem RHS not `true`") in
  internal_error func;;


(* undisch_rule : thm -> thm                                                  *)
(*                                                                            *)
(* This is the undischarge rule.  It takes an implication theorem, and        *)
(* removes the antecedent from the conclusion and adds it to the assumptions. *)
(*                                                                            *)
(*    A |- p ==> q                                                            *)
(*    ------------                                                            *)
(*    A u {p} |- q                                                            *)

let undisch_rule th =              (* A |- p ==> q     *)
 try
  let (tm1,_) = dest_imp (concl th) in
  let th1 = assume_rule tm1 in            (* {p} |- p         *)
  mp_rule th th1                          (* A u {p} |- q     *)
 with HolFail _ ->
  let func = "undisch_rule" in
  let () = assert1 (is_imp (concl th))     (func,"Not an implication term") in
  internal_error func;;


(* add_asm_rule : term -> thm -> thm                                          *)
(*                                                                            *)
(* This is the assumption insertion rule.  It takes a boolean term and a      *)
(* theorem, and returns the same theorem but with the supplied term added to  *)
(* its assumptions.  The returned theorem is the inputted theorem if the term *)
(* is already in the assumptions.                                             *)
(*                                                                            *)
(*    `q`   A |- p                                                            *)
(*    ------------                                                            *)
(*    A u {q} |- p                                                            *)

let add_asm_rule tm th =          (* A |- p          *)
 try
  let th1 = disch_rule tm th in            (* A\{q} |- q ==> p          *)
  undisch_rule th1                         (* A u {q} |- p              *)
 with HolFail _ ->
  let func = "add_asm_rule" in
  let () = assert1 (is_bool_term tm)       (func,"Arg 1 not a boolean term") in
  internal_error func;;


(* prove_asm_rule : thm -> thm -> thm                                         *)
(*                                                                            *)
(* This is the assumption proving rule.  It takes two theorems, and returns   *)
(* the second theorem but with the conclusion of the first theorem removed    *)
(* from the assumptions (if present) and the assumptions from the first       *)
(* theorem added.  Note that the first theorem's conclusion does not have to  *)
(* be in the second's assumptions for the rule to succeed.                    *)
(*                                                                            *)
(*    A1 |- p    A2 |- q                                                      *)
(*    ------------------                                                      *)
(*    A1 u (A2\{p}) |- q                                                      *)

let prove_asm_rule th01 th02 =      (* A1 |- p    A2 |- q    *)
  let th1 = disch_rule (concl th01) th02 in    (* A2\{p} |- p ==> q      *)
  mp_rule th1 th01;;                           (* A1 u A2\{p} |- q       *)


(* eq_imp_rule1 : thm -> thm * thm                                            *)
(*                                                                            *)
(* This is the first equivalence elimination rule.  It takes a theorem        *)
(* stating the equivalence of two boolean terms, and returns a theorem        *)
(* stating that the LHS implies the RHS, under the same assumptions.          *)
(*                                                                            *)
(*    A |- p <=> q                                                            *)
(*    ------------                                                            *)
(*    A |- p ==> q                                                            *)

let eq_imp_rule1 th =       (* A |- p <=> q      *)
 try
  let tm1 = eqthm_lhs th in
  let th1 = eq_mp_rule th (assume_rule tm1) in          (* A u {p} |- q     *)
  let th2 = disch_rule tm1 th1 in                       (* A\{p} |- p ==> q *)
  if (mem' alpha_eq tm1 (asms th))
    then add_asm_rule tm1 th2                           (* A |- p ==> q     *)
    else th2                                            (* A |- p ==> q     *)
 with HolFail _ ->
  let func = "eq_imp_rule1" in
  let () = assert1 (is_bool_eqthm th)      (func,"Not a bool equality thm") in
  internal_error func;;


(* eq_imp_rule2 : thm -> thm * thm                                            *)
(*                                                                            *)
(* This is the second equivalence elimination rule.  It takes a theorem       *)
(* stating the equivalence of two boolean terms, and returns a theorem        *)
(* stating that the RHS implies the LHS, under the same assumptions.          *)
(*                                                                            *)
(*    A |- p <=> q                                                            *)
(*    ------------                                                            *)
(*    A |- q ==> p                                                            *)

let eq_imp_rule2 th =       (* A |- p <=> q      *)
 try
  let tm2 = eqthm_rhs th in
  let th1 = eq_mp_rule (eq_sym_rule th)
                       (assume_rule tm2) in             (* A u {q} |- p      *)
  let th2 = disch_rule tm2 th1 in                       (* A\{q} |- q ==> p  *)
  if (mem' alpha_eq tm2 (asms th))
    then add_asm_rule tm2 th2                           (* A |- q ==> p     *)
    else th2                                            (* A |- q ==> p     *)
 with HolFail _ ->
  let func = "eq_imp_rule2" in
  let () = assert1 (is_bool_eqthm th)      (func,"Not a bool equality thm") in
  internal_error func;;


(* not_intro_rule : thm -> thm                                                *)
(*                                                                            *)
(* This is the logical negation introduction rule.  It takes an implication   *)
(* theorem where the RHS is falsity, and returns the logical negation of the  *)
(* LHS, under the same assumptions.                                           *)
(*                                                                            *)
(*    A |- p ==> false                                                        *)
(*    ----------------                                                        *)
(*        A |- ~ p                                                            *)

let not_intro_rule th =           (* A |- p ==> false   *)
 try
  let p = fst (dest_imp (concl th)) in
  let th1 = app_beta_rhs_rule not_def p in   (* |- ~ p <=> p ==> false  *)
  eq_mp_rule (eq_sym_rule th1) th            (* A |- ~ p                *)
 with HolFail _ ->
  let func = "not_intro_rule" in
  let (p,f) = try1 dest_imp (concl th)   (func,"Not an implication theorem") in
  let () = assert1 (term_eq f false_tm)  (func,"Theorem RHS not `false`") in
  internal_error func;;


(* not_elim_rule : thm -> thm                                                 *)
(*                                                                            *)
(* This is the logical negation elimination rule.  It takes a logical         *)
(* negation theorem, and returns an implication with the negated term on the  *)
(* LHS and falsity on the RHS, under the same assumptions.                    *)
(*                                                                            *)
(*        A |- ~ p                                                            *)
(*    ----------------                                                        *)
(*    A |- p ==> false                                                        *)

let not_elim_rule th =           (* A |- ~ p      *)
 try
  let p = dest_not (concl th) in
  let th1 = app_beta_rhs_rule not_def p in  (* |- ~ p <=> p ==> false  *)
  eq_mp_rule th1 th                         (* A |- p ==> false        *)
 with HolFail _ ->
  let func = "not_elim_rule" in
  let () = assert1 (is_not (concl th))      (func,"Not a negation theorem") in
  internal_error func;;


(* deduct_contrapos_rule : term -> thm -> thm                                 *)
(*                                                                            *)
(* This is the contraposition rule for deduction.  It swaps and logically     *)
(* negates the supplied assumption term and the conclusion of the supplied    *)
(* theorem.  Note that the supplied term does not have to be present in the   *)
(* assumptions of the supplied theorem for the rule to succeed.  If the       *)
(* logical negation of the supplied theorem's conclusion is the supplied      *)
(* term, then it will not occur in the resulting theorem's assumptions.       *)
(*                                                                            *)
(*        `q`   A |- p                                                        *)
(*    ---------------------                                                   *)
(*    (A u {~p})\{q} |- ~ q                                                   *)

let deduct_contrapos_rule tm1 th =         (* A |- p         *)
  let tm2 = concl th in
  (* (A u {~ p}) \ {q} |- ~ q       *)
  not_intro_rule
    (disch_rule tm1
      (* A u {~ p} |- false           *)
      (mp_rule
        (* ~ p |- p ==> false           *)
        (not_elim_rule (assume_rule (mk_not tm2)))
        th ));;


(* eqf_elim_rule : thm -> thm                                                 *)
(*                                                                            *)
(* The is the falsity equivalence elimination rule.  It takes an equality     *)
(* theorem with falsity on the RHS, and returns the logical negation of the   *)
(* LHS, under the same assumptions.                                           *)
(*                                                                            *)
(*    A |- p <=> false                                                        *)
(*    ----------------                                                        *)
(*        A |- ~ p                                                            *)

let eqf_elim_rule th  =         (* A |- p <=> false   *)
 try
  let th1 = eq_imp_rule1 th in              (* A |- p ==> false        *)
  not_intro_rule th1                        (* A |- ~ p                *)
 with HolFail _ ->
  let func = "eqf_elim_rule" in
  let (_,tm2) = try1 dest_eqthm th   (func,"Not a boolean equality theorem") in
  let () = assert1 (term_eq tm2 false_tm)   (func,"Theorem RHS not `false`") in
  internal_error func;;


(* imp_trans_rule : thm -> thm -> thm                                         *)
(*                                                                            *)
(* This is the transitivity rule for implication.  It takes two implication   *)
(* theorem arguments, where the first theorem's RHS is the same (modulo       *)
(* alpha-equivalence) as the second theorem's LHS.  It returns a theorem      *)
(* stating that the first theorem's LHS implies the second theorem's RHS,     *)
(* under the unioned assumptions of the two theorems.                         *)
(*                                                                            *)
(*    A1 |- p ==> q    A2 |- q ==> r                                          *)
(*    ------------------------------                                          *)
(*          A1 u A2 |- p ==> r                                                *)

let imp_trans_rule tha thb =      (* A1 |- p ==> q    A2 |- q ==> r   *)
 try
  let (tm1,_) = dest_imp (concl tha) in
  let th1 = assume_rule tm1 in            (* p |- p                   *)
  let th2 = mp_rule tha th1 in            (* A1 u {p} |- q            *)
  let th3 = mp_rule thb th2 in            (* A1 u A2 u {p} |- r       *)
  let th4 = disch_rule tm1 th3 in         (* (A1 u A2)\{p} |- p ==> r *)
  if (mem' alpha_eq tm1 (asms tha)) || (mem' alpha_eq tm1 (asms thb))
    then add_asm_rule tm1 th4             (* A1 u A2 |- p ==> r       *)
    else th4                              (* A1 u A2 |- p ==> r       *)
 with HolFail _ ->
  let func = "imp_trans_rule" in
  let (_,tm2) = try1 dest_imp (concl tha)
                                   (func,"Arg 1 not an implication theorem") in
  let (tm2',_) = try1 dest_imp (concl thb)
                                   (func,"Arg 2 not an implication theorem") in
  let () = assert1 (alpha_eq tm2 tm2')
           (func,"1st theorem RHS and 2nd theorem LHS not alpha-equivalent") in
  internal_error func;;

let list_imp_trans_rule ths = foldl1 imp_trans_rule ths;;


(* spec_rule : term -> thm -> thm                                             *)
(*                                                                            *)
(* This is the universal elimination rule.  It strips off the outermost       *)
(* universal quantifier from the supplied theorem, and replaces in the body   *)
(* each occurrence of the stripped binding variable with the supplied term.   *)
(* The type of the supplied term must equal the type of the stripped binding  *)
(* variable.                                                                  *)
(*                                                                            *)
(*    `t`   A |- !x. p                                                        *)
(*    ----------------                                                        *)
(*      A |- p[t/x]                                                           *)

let spec_rule tm th =             (* x     A |- !x. p        *)
 try
  let (v,p) = dest_forall (concl th) in
  let tm0 = mk_abs (v,p) in
  let ty = type_of v in
  let th1 = app_beta_rhs_rule (inst_type_rule [(a_ty,ty)] forall_def) tm0 in
                                     (* |- (!x. p) <=> (\x. p) = (\x. true)  *)
  let th2 = eq_mp_rule th1 th in     (* A |- (\x. p) = (\x. true)            *)
  let th3 = app_beta_rule th2 tm in  (* A |- p[t/x] <=> true                 *)
  eqt_elim_rule th3                  (* A |- p[t/x]                          *)
 with HolFail _ ->
  let func = "spec_rule" in
  let (v,_) = try1 dest_forall (concl th)
                                   (func,"Arg 2 not a universal theorem") in
  let () = assert1 (same_types tm v)
                                   (func,"Supplied term's type not equal to \
                                          universal's binding var type") in
  internal_error func;;


(* list_spec_rule : term list -> thm -> thm                                   *)
(*                                                                            *)
(* This is the compound universal elimination rule.  It strips off an         *)
(* outermost universal quantifier from the supplied theorem for each item in  *)
(* the supplied term list, replacing each occurrence of a stripped binding    *)
(* variable in the body with its corresponding item in the term list.  The    *)
(* type of each term in the term list must equal the type of its              *)
(* corresponding binding variable.                                            *)
(*                                                                            *)
(*    [`t1`;`t2`;..]   A |- !x1 x2 .. . p                                     *)
(*    -----------------------------------                                     *)
(*           A |- p[t1/x1;t2/x2;..]                                           *)

let list_spec_rule tms th =
 try
  foldl (swap_arg spec_rule) th tms
 with HolFail _ ->
  let func = "list_spec_rule" in
  let vs = try1 (fst <* cut (length tms) <* fst <* strip_forall <* concl) th
             (func,"Supplied theorem has too few universal binding vars") in
  let nvtms = enumerate (zip vs tms) in
  let foo (n,(v,tm)) =
         assert1 (same_types tm v)
            (func, "Type of supplied term " ^ string_of_int n ^ " not equal " ^
                   "to universal's corresponding binding var's type") in
  let _ = map foo nvtms in
  internal_error func;;


(* spec_all_rule : thm -> thm                                                 *)
(*                                                                            *)
(* This is the compound default universal elimination rule.  It strips off    *)
(* all the outer universal quantifiers from the supplied theorem.  Note that  *)
(* the supplied theorem does not have to be a universal quantification for    *)
(* the rule to succeed (in which case the resulting theorem is the same as    *)
(* the supplied theorem).                                                     *)
(*                                                                            *)
(*    A |- !x1 x2 .. xn. p                                                    *)
(*    --------------------                                                    *)
(*           A |- p                                                           *)

let spec_all_rule th =
  let vs = (fst <* strip_forall <* concl) th in
  list_spec_rule vs th;;


(* bspec_rule : term -> thm -> thm                                            *)
(*                                                                            *)
(* This is the beta-reducing universal elimination rule.  It strips off the   *)
(* outermost universal quantifier from the supplied theorem, and replaces in  *)
(* the body each occurrence of the stripped binding variable with the         *)
(* supplied term.  If the supplied term is a lambda abstraction, it also      *)
(* performs beta-reduction on each substituted occurrence that is applied to  *)
(* an argument.  The type of the supplied term must equal the type of the     *)
(* stripped binding variable.                                                 *)
(*                                                                            *)
(*          `\y. t`   A |- !x. p                                              *)
(*    --------------------------------                                        *)
(*    A |- p[ \y.t / x; t[s/y] / x s ]                                        *)

let beta_patt_conv vsp tmp tm =
  let rec bp_conv bvs tmp tm =
     if (is_comb tmp) &&
        (let fp = fst (strip_comb tmp) in
         (is_var fp) && (mem fp vsp) && not (mem fp bvs))
       then let (fp,argps) = strip_comb tmp in
            let (f,args) = strip_comb tm in
            let (args0,args') = cut (length args - length argps) args in
            let f' = list_mk_comb (f,args0) in
            list_app_beta_rhs_rule (eq_refl_conv f') args'
       else match (dest_term tmp, dest_term tm) with
              ((Term_var _ | Term_const _), _)
                 -> raise LocalFail
            | (Term_comb (tmp1,tmp2), Term_comb (tm1,tm2))
                 -> (try
                       let th1 = bp_conv bvs tmp1 tm1 in
                       (try
                          let th2 = bp_conv bvs tmp2 tm2 in
                          mk_comb_rule th1 th2
                        with LocalFail ->
                          mk_comb1_rule th1 tm2)
                     with LocalFail ->
                       let th2 = bp_conv bvs tmp2 tm2 in
                       mk_comb2_rule tm1 th2)
            | (Term_abs (vp,tmp0), Term_abs (v,tm0))
                 -> let bvs' = insert vp bvs in
                    mk_abs_rule v (bp_conv bvs' tmp0 tm0)
            | (_, _)
                 -> internal_error "patt_conv" in
  bp_conv [] tmp tm;;

let beta_patt_rule vsp tmp th = conv_rule (beta_patt_conv vsp tmp) th;;

let bspec_rule tm th =
  let th1 = try2 (spec_rule tm) th    "bspec_rule" in
  if (is_abs tm)
    then let (v0,tm0) = dest_forall (concl th) in
         beta_patt_rule [v0] tm0 th1
    else th1;;

let list_bspec_rule tms th = foldl (swap_arg bspec_rule) th tms;;


(* contr_rule : term -> thm -> thm                                            *)
(*                                                                            *)
(* This is the intuitionistic contradiction rule.  It takes a boolean term    *)
(* and a theorem with falsity as its conclusion.  It returns a theorem with   *)
(* the supplied term as its conclusion, under the same assumptions as the     *)
(* supplied theorem.                                                          *)
(*                                                                            *)
(*    `p`   A |- false                                                        *)
(*    ----------------                                                        *)
(*         A |- p                                                             *)

let contr_rule tm th =            (* p     A |- false      *)
 try
  let () = assert0 (term_eq (concl th) false_tm)     LocalFail in
  let th1 = eq_mp_rule false_def (assume_rule false_tm) in  (* false |- !t. t *)
  let th2 = spec_rule tm th1 in                             (* false |- p     *)
  prove_asm_rule th th2                                     (* A |- p         *)
 with HolFail _ | LocalFail ->
  let func = "contr_rule" in
  let () = assert1 (is_bool_term tm)    (func,"Arg 1 not a boolean term") in
  let () = assert1 (term_eq (concl th) false_tm)
                                        (func,"Arg 2 conclusion not `false`") in
  internal_error func;;


(* eta_conv : term -> thm                                                     *)
(*                                                                            *)
(* This is the eta reduction conversion.  It takes a lambda abstraction term, *)
(* where the body is a function application, and the binding variable is the  *)
(* argument subterm of the function application and not free in the function  *)
(* subterm.  It returns a theorem stating that the term is equal to the       *)
(* function subterm, under no assumptions.                                    *)
(*                                                                            *)
(*       `\x. f x`                                                            *)
(*    ----------------                                                        *)
(*    |- (\x. f x) = f                                                        *)

let eta_conv tm =
 try
  let (v,tm0) = dest_abs tm in
  let (f,v0) = dest_comb tm0 in
  let (ty1,ty2) = dest_fun_type (type_of f) in
  let th1 = spec_rule f (inst_type_rule [(a_ty,ty1);(b_ty,ty2)] eta_ax) in
                                                   (* |- (\x. f x) = f       *)
  let th2 = eq_trans_rule (eq_refl_conv tm) th1 in (* |- (\v. f v) = f       *)
  th2
 with HolFail _ ->
  let func = "eta_conv" in
  let (v,tm0) = try1 dest_abs tm      (func,"Not a lambda abstraction term") in
  let (f,v0) = try1 dest_comb tm0
                 (func,"Lambda abstraction body not a function application") in
  let () = assert1 (term_eq v0 v)
                     (func,"Argument subterm of lambda abstraction body \
                            not equal to binding var") in
  let () = assert1 (not (var_free_in v f))
                     (func,"Abstraction var occurs free in function subterm \
                            of lambda abstraction body") in
  internal_error func;;


(* imp_antisym_rule : thm -> thm -> thm                                       *)
(*                                                                            *)
(* This is the antisymmetry rule for implication.  It takes two implication   *)
(* theorem arguments, where the LHS of each is the same (modulo alpha-        *)
(* equivalence) as the RHS of the other.  It returns a theorem stating the    *)
(* logical equivalence of the two sides, under the unioned assumptions.       *)
(*                                                                            *)
(*    A1 |- p ==> q    A2 |- q ==> p                                          *)
(*    ------------------------------                                          *)
(*          A1 u A2 |- p <=> q                                                *)

let imp_antisym_rule th01 th02 =    (* A1 |- p ==> q    A2 |- q ==> p   *)
 try
  let (tm1,tm2) = dest_imp (concl th01) in
  let th1 = list_spec_rule [tm1;tm2] imp_antisym_ax in
                             (* |- (p ==> q) ==> (q ==> p) ==> (p <=> q) *)
  mp_rule (mp_rule th1 th01) th02      (* |- p <=> q                     *)
 with HolFail _ ->
  let func = "imp_antisym_rule" in
  let (tm1,tm2) = try1 dest_imp (concl th01)
                                   (func,"Arg 1 not an implication theorem") in
  let (tm2',tm1') = try1 dest_imp (concl th02)
                                   (func,"Arg 2 not an implication theorem") in
  let () = assert1 (alpha_eq tm1' tm1)
           (func,"1st theorem LHS and 2nd theorem RHS not alpha-equivalent") in
  let () = assert1 ((alpha_eq tm1' tm1) && (alpha_eq tm2' tm2))
           (func,"1st theorem RHS and 2nd theorem LHS not alpha-equivalent") in
  internal_error func;;


(* deduct_antisym_rule : thm -> thm -> thm                                    *)
(*                                                                            *)
(* This is the antisymmetry rule for deduction.  It takes two theorem         *)
(* arguments.  It returns a theorem stating that the supplied conclusions are *)
(* equivalent, under the unioned assumptions but with each theorem's          *)
(* conclusion removed from the other's assumptions.                           *)
(*                                                                            *)
(*        A1 |- p    A2 |- q                                                  *)
(*    --------------------------                                              *)
(*    A1\{q} u A2\{p} |- p <=> q                                              *)

let deduct_antisym_rule th01 th02 =      (* A1 |- p     A2 |- q   *)
  let th1 = disch_rule (concl th02) th01 in    (* A1\{q} |- q ==> p          *)
  let th2 = disch_rule (concl th01) th02 in    (* A2\{p} |- p ==> q          *)
  imp_antisym_rule th2 th1;;                   (* A1\{q} u A2\{p} |- p <=> q *)


(* eq_sym_conv : term -> thm                                                  *)
(*                                                                            *)
(* This is the symmetry conversion for equality.  It transforms the supplied  *)
(* equality term by swapping its LHS with its RHS, under no assumptions.      *)
(*                                                                            *)
(*           `t1 = t2`                                                        *)
(*    ----------------------                                                  *)
(*    |- t1 = t2 <=> t2 = t1                                                  *)

let eq_sym_conv tm =                  (* t1 = t2      *)
 try
  let th1 = eq_sym_rule (assume_rule tm) in   (* t1 = t2 |- t2 = t1       *)
  let tm' = concl th1 in
  let th2 = eq_sym_rule (assume_rule tm') in  (* t2 = t1 |- t1 = t2       *)
  deduct_antisym_rule th2 th1                 (* |- t1 = t2 <=> t2 = t1   *)
 with HolFail _ ->
  let func = "eq_sym_conv" in
  let () = assert1 (is_eq tm)       (func,"Not an equality term") in
  internal_error func;;


(* eqt_intro_rule : thm -> thm                                                *)
(*                                                                            *)
(* This is the truth equivalence introduction rule.  It takes any theorem,    *)
(* and returns the theorem stating that the conclusion is equivalent to       *)
(* truth, under the same assumptions.                                         *)
(*                                                                            *)
(*         A |- p                                                             *)
(*    ---------------                                                         *)
(*    A |- p <=> true                                                         *)

let eqt_intro_rule th =            (* A |- p      *)
 try
  let p = concl th in
  let th1 = list_spec_rule [p;true_tm] imp_antisym_ax in
                      (* |- (p ==> true) ==> (true ==> p) ==> (p <=> true)   *)
  let th2 = disch_rule p truth_thm in         (* |- p ==> true               *)
  let th3 = disch_rule true_tm th in          (* A |- true ==> p             *)
  mp_rule (mp_rule th1 th2) th3               (* A |- p <=> true             *)
 with HolFail _ -> internal_error "eqt_intro_rule";;


(* eqf_intro_rule : thm -> thm                                                *)
(*                                                                            *)
(* This is the falsity equivalence introduction rule.  It takes a theorem     *)
(* with logical negation at its top level, and returns a theorem stating that *)
(* the body of the negation is equivalent to falsity, under the same          *)
(* assumptions.                                                               *)
(*                                                                            *)
(*        A |- ~ p                                                            *)
(*    ----------------                                                        *)
(*    A |- p <=> false                                                        *)

let eqf_intro_rule th =            (* A |- ~ p    *)
 try
  let p = dest_not (concl th) in
  let th1 = not_elim_rule th in                       (* A |- p ==> false    *)
  let th2 = eq_mp_rule false_def (assume_rule false_tm) in
                                                      (* false |- !p. p      *)
  let th3 = spec_rule p th2 in                        (* false |- p          *)
  let th4 = disch_rule false_tm th3 in                (* |- false ==> p      *)
  imp_antisym_rule th1 th4                            (* A |- p <=> false    *)
 with HolFail _ ->
  let func = "eqf_intro_rule" in
  let () = assert1 (is_not (concl th))      (func,"Not a negation term") in
  internal_error func;;


(* gen_rule : term -> thm -> thm                                              *)
(*                                                                            *)
(* This is the universal introduction rule.  It universally quantifies the    *)
(* supplied theorem with the supplied binding variable, under the same        *)
(* assumptions.  The binding variable must not occur free in the assumptions. *)
(*                                                                            *)
(*    `x`   A |- p         [ "x" not free in `A` ]                            *)
(*    ------------                                                            *)
(*     A |- !x. p                                                             *)

let gen_rule v th =               (* A |- p        *)
 try
  let p = concl th in
  let ty = type_of v in
  let tm1 = mk_abs (v,p) in
  let th1 = mk_abs_rule v (eqt_intro_rule th) in
                                      (* A |- (\x. p) = (\x. true)           *)
  let th2 = app_beta_rhs_rule (inst_type_rule [(a_ty,ty)] forall_def) tm1 in
                                      (* |- (!x. p) <=> (\x. p) = (\x. true) *)
  eq_mp_rule (eq_sym_rule th2) th1    (* A |- !x. p                          *)
 with HolFail _ ->
  let func = "gen_rule" in
  let () = assert1 (is_var v)         (func,"Arg 1 not a variable") in
  let () = assert1 (not (exists (var_free_in v) (asms th)))
                      (func,"Supplied variable occurs free in assumptions") in
  internal_error func;;

let list_gen_rule tms th = foldr gen_rule tms th;;


(* conj_rule : thm -> thm -> thm                                              *)
(*                                                                            *)
(* This is the conjunction introduction rule.  It conjoins the two supplied   *)
(* theorems and unions their assumptions.                                     *)
(*                                                                            *)
(*    A1 |- p    A2 |- q                                                      *)
(*    ------------------                                                      *)
(*    A1 u A2 |- p /\ q                                                       *)

let conj_lemma0 =
  (* |- p1_ /\ p2_ <=> (!p. (p1_ ==> p2_ ==> p) ==> p)     *)
  list_app_beta_rhs_rule conj_def [p1_;p2_];;

let conj_lemma =
  (* |- p1_ ==> p2_ ==> p1_ /\ p2_   *)
  disch_rule p1_
    (disch_rule p2_
      (* p1_, p2_ |- p1_ /\ p2_          *)
      (eq_mp_rule
        (eq_sym_rule conj_lemma0)
        (* p1_, p2_ |- !p. (p1_ ==> p2_ ==> p) ==> p    *)
        (gen_rule p
          (disch_rule `p1_ ==> p2_ ==> p`
            (* p1_, p2_, p1_ ==> p2_ ==> p |- p             *)
            (mp_rule (mp_rule (assume_rule `p1_ ==> p2_ ==> p`)
                              (assume_rule p1_))
                     (assume_rule p2_) )))));;

let conj_rule th01 th02 =     (* A1 |- p    A2 |- q   *)
 try
  let p = concl th01  and q = concl th02 in
  let th1 = inst_rule [(p1_,p);(p2_,q)] conj_lemma in (* |- p ==> q ==> p /\ q*)
  mp_rule (mp_rule th1 th01) th02                     (* A1uA2 |- p /\ q      *)
 with HolFail _ -> internal_error "conj_rule";;


(* conjunct1_rule : thm -> thm                                                *)
(*                                                                            *)
(* This is the conjunction elimination rule for the LHS.  It removes the RHS  *)
(* conjunct from the supplied conjunction theorem.                            *)
(*                                                                            *)
(*    A |- p /\ q                                                             *)
(*    -----------                                                             *)
(*      A |- p                                                                *)

let conjunct1_lemma =
  (* |- p1_ /\ p2_ ==> p1_             *)
  disch_rule `p1_ /\ p2_`
    (mp_rule
      (* p1_ /\ p2_ |- (p1_ ==> p2_ ==> p1_) ==> p1_   *)
      (spec_rule p1_ (eq_mp_rule conj_lemma0 (assume_rule `p1_ /\ p2_`)))
      (* |- p1_ ==> p2_ ==> p1_                        *)
      (disch_rule p1_ (disch_rule p2_ (assume_rule p1_))) );;

let conjunct1_rule th =          (* A |- p /\ q       *)
 try
  let (p,q) = dest_conj (concl th) in
  let th1 = inst_rule [(p1_,p);(p2_,q)] conjunct1_lemma in (* |- p /\ q ==> p *)
  mp_rule th1 th                                           (* A |- p          *)
 with HolFail _ ->
  let func = "conjunct1_rule" in
  let () = assert1 (is_conj (concl th))    (func,"Not a conjunction theorem") in
  internal_error func;;


(* conjunct2_rule : thm -> thm                                                *)
(*                                                                            *)
(* This is the conjunction elimination rule for the RHS.  It removes the LHS  *)
(* conjunct from the supplied conjunction theorem.                            *)
(*                                                                            *)
(*    A |- p /\ q                                                             *)
(*    -----------                                                             *)
(*      A |- q                                                                *)

let conjunct2_lemma =
  (* |- p1_ /\ p2_ ==> p2_             *)
  disch_rule `p1_ /\ p2_`
    (mp_rule
      (* p1_ /\ p2_ |- (p1_ ==> p2_ ==> p2_) ==> p2_    *)
      (spec_rule p2_
         (eq_mp_rule conj_lemma0 (assume_rule `p1_ /\ p2_`)))
      (* |- p1_ ==> p2_ ==> p2_                         *)
      (disch_rule p1_ (disch_rule p2_ (assume_rule p2_))) );;

let conjunct2_rule th =          (* A |- p /\ q       *)
 try
  let (p,q) = dest_conj (concl th) in
  let th1 = inst_rule [(p1_,p);(p2_,q)] conjunct2_lemma in (* |- p /\ q ==> q *)
  mp_rule th1 th                                           (* A |- q          *)
 with HolFail _ ->
  let func = "conjunct2_rule" in
  let () = assert1 (is_conj (concl th))   (func,"Not a conjunction theorem") in
  internal_error func;;


(* disj_cases_rule : thm -> thm -> thm -> thm                                 *)
(*                                                                            *)
(* This is the disjunction elimination rule.  It takes a disjunction theorem  *)
(* and two extra theorems that share the same conclusion.  It returns a       *)
(* theorem with the same conclusion as the extra theorems.  The assumptions   *)
(* of the returned theorem union the assumptions of the extra theorems, but   *)
(* with the disjunction theorem's LHS removed from the first's assumptions    *)
(* and its RHS removed from the second's, unioned together with the           *)
(* disjunction theorem's assumptions.                                         *)
(*                                                                            *)
(*    A |- p \/ q    A1 |- r    A2 |- r                                       *)
(*    ---------------------------------                                       *)
(*        A u A1\{p} u A2\{q} |- r                                            *)

let disj_lemma0 =
  list_app_beta_rhs_rule disj_def [p1_;p2_];;
                (* |- p1_ \/ p2_ <=> (!p. (p1_ ==> p) ==> (p2_ ==> p) ==> p)  *)

let disj_cases_lemma =
  (* |- p1_ \/ p2_ ==> (p1_ ==> p_) ==> (p2_ ==> p_) ==> p_  *)
  disch_rule`p1_ \/ p2_`
   (spec_rule p_
     (* p1_ \/ p2_ |- !p. (p1_ ==> p) ==> (p2_ ==> p) ==> p      *)
     (eq_mp_rule disj_lemma0 (assume_rule `p1_ \/ p2_`)));;

let disj_cases_rule th0 th01 th02 =   (* A0 |- p \/ q    A1 |- r    A2 |- r  *)
 try
  let (p,q) = dest_disj (concl th0) in
  let r = concl th01 in
  let th1 = disch_rule p th01 in               (* A1\{p} |- p ==> t       *)
  let th2 = disch_rule q th02 in               (* A2\{q} |- q ==> r       *)
  let th3 = inst_rule [(p1_,p);(p2_,q);(p_,r)] disj_cases_lemma in
                             (* |- p \/ q ==> (p ==> r) ==> (q ==> r) ==> r  *)
  mp_rule (mp_rule (mp_rule th3 th0) th1) th2  (* A0 u A1\{p} u A2\{q} |- r  *)
 with HolFail _ ->
  let func = "disj_cases_rule" in
  let () = assert1 (is_disj (concl th0))
                                    (func,"Arg 1 not a disjunction theorem") in
  let () = assert1 (concl th01 = concl th02)
                   (func,"Arg 2 and Arg 3 conclusions not alpha-equivalent") in
  internal_error func;;


(* disj1_rule : thm -> term -> thm                                            *)
(*                                                                            *)
(* This is the disjunction introduction rule for the LHS.  It disjoins the    *)
(* supplied boolean term to the RHS of the supplied theorem.                  *)
(*                                                                            *)
(*    A |- p   `q`                                                            *)
(*    ------------                                                            *)
(*    A |- p \/ q                                                             *)

let disj1_lemma =
  (* |- p1_ ==> p1_ \/ p2_        *)
  disch_rule p1_
    (eq_mp_rule
      (eq_sym_rule disj_lemma0)
      (* p1_ |- !p. (p1_ ==> p) ==> (p2_ ==> p) ==> p        *)
      (gen_rule p
        (disch_rule `p1_ ==> p`
          (disch_rule `p2_ ==> p`
            (* p1_ ==> p, p1_ |- p                               *)
            (mp_rule (assume_rule `p1_ ==> p`) (assume_rule p1_)) ))));;

let disj1_rule th tm =             (* A |- p    q   *)
 try
  let p = concl th  and q = tm in
  let th1 = inst_rule [(p1_,p);(p2_,q)] disj1_lemma in
  mp_rule th1 th                   (* A |- p \/ q   *)
 with HolFail _ ->
  let func = "disj1_rule" in
  let () = assert1 (is_bool_term tm)      (func,"Arg 2 not a boolean term") in
  internal_error func;;


(* disj2_rule : term -> thm -> thm                                            *)
(*                                                                            *)
(* This is the disjunction introduction rule for the RHS.  It disjoins the    *)
(* supplied boolean term to the LHS of the supplied theorem.                  *)
(*                                                                            *)
(*    `p`   A |- q                                                            *)
(*    ------------                                                            *)
(*    A |- p \/ q                                                             *)

let disj2_lemma =
  (* |- q ==> p \/ q                         *)
  disch_rule p2_
    (eq_mp_rule
      (eq_sym_rule disj_lemma0)
      (* p2_ |- !p. (p1_ ==> p) ==> (p2_ ==> p) ==> p    *)
      (gen_rule p
        (disch_rule `p1_ ==> p`
          (disch_rule `p2_ ==> p`
            (* p2_ ==> p, p2_ |- p                         *)
            (mp_rule (assume_rule `p2_ ==> p`) (assume_rule p2_)) ))));;

let disj2_rule tm th =             (* p    A |- q   *)
 try
  let p = tm  and q = concl th in
  let th1 = inst_rule [(p1_,p);(p2_,q)] disj2_lemma in
  mp_rule th1 th                   (* A |- p \/ q   *)
 with HolFail _ ->
  let func = "disj2_rule" in
  let () = assert1 (is_bool_term tm)      (func,"Arg 1 not a boolean term") in
  internal_error func;;


(* choose_rule : term * thm -> thm -> thm                                     *)
(*                                                                            *)
(* This is the existential elimination rule.  It removes, from the            *)
(* assumptions of a supplied main theorem, the body of a supplied existential *)
(* theorem (but with all occurrences of the binding variable replaced with a  *)
(* supplied variable), and adds the assumptions of the existential theorem.   *)
(* The supplied variable is not allowed to be free in existential theorem's   *)
(* conclusion or in the original main theorem's other assumptions or its      *)
(* conclusion.  Note that the altered body of the existential theorem does    *)
(* not have to be present in the assumptions of the main theorem for the rule *)
(* to succeed.                                                                *)
(*                                                                            *)
(*    `y`   A1 |- ?x. p    A2 |- q      [ "y" not free in:                    *)
(*    ----------------------------          `?x. p`, `q` or `A2\{p[y/x]}` ]   *)
(*        A1 u A2\{p[y/x]} |- q                                               *)

let choose_rule (v,th0) th =       (* y    A1 |- ?x. p    A2 |- q   *)
  let ty = type_of v in
  let (hs,q) = dest_thm th in
  let tm0 = concl th0 in
 try
  let (u,p) = dest_exists (concl th0) in
  let tm1 = mk_abs (u,p) in
  let p' = var_inst [(u,v)] p in
  let hs' = subtract' alpha_eq hs [p'] in
  let () = assert0 (not (exists (var_free_in v) (tm0::q::hs')))    LocalFail in
  let th1 = app_beta_rhs_rule (inst_type_rule [(a_ty,ty)] exists_def) tm1 in
                                          (* |- (?x. p) <=> (\x. p) (@x. p)  *)
  let th2 = eq_mp_rule th1 th0 in         (* A1 |- (\x. p) (@ x. p)          *)
  let tm2 = mk_comb (tm1,v) in
  let th3 = beta_conv tm2 in              (* |- (\x. p) y <=> p[y/x]         *)
  let th4 = eq_imp_rule1 th3 in           (* |- (\x. p) y ==> p[y/x]         *)
  let th5 = disch_rule p' th in           (* A2\{p[y/x]} |- p[y/x] ==> q     *)
  let th6 = imp_trans_rule th4 th5 in     (* A2\{p[y/x]} |- (\x. p) y ==> q  *)
  let tm3 = rand (concl th2) in
  let th7 = inst_rule [(v,tm3)] th6 in
                                     (* A2\{p[y/x]} |- (\x. p) (@x. p) ==> q *)
  mp_rule th7 th2                         (* A1 u A2\{p[y/x]} |- q           *)
 with HolFail _ | LocalFail ->
  let func = "choose_rule" in
  let () = assert1 (is_var v)                (func,"Arg 1 not a variable") in
  let (u,p) = try1 dest_exists (concl th0)
                                   (func,"Arg 2 not an existential theorem") in
  let () = assert1 (same_types v u)
                     (func,"Supplied variable's type \
                            not equal to existential's binding var type") in
  let p' = var_inst [(u,v)] p in
  let hs' = subtract' alpha_eq hs [p'] in
  let () = assert1 (not (var_free_in v tm0))
               (func,"Supplied variable occurs free in \
                                        existential theorem's concluction") in
  let () = assert1 (not (var_free_in v q))
               (func,"Supplied variable occurs free in main theorem's concl") in
  let () = assert1 (not (exists (var_free_in v) hs'))
               (func,"Supplied variable occurs free in \
                                        main theorem's other assumptions") in
  internal_error func;;


(* fun_eq_thm : thm                                                           *)
(*                                                                            *)
(*    |- !f g. f = g <=> (!x. f x = g x)                                      *)

let fun_eq_thm = save_thm ("fun_eq_thm",
  let x = `x:'a` and f = `f:'a->'b` and g = `g:'a->'b` in
  (* |- !f g. f = g <=> (!x. f x = g x) *)
  (list_gen_rule [f;g]
    (deduct_antisym_rule
      (* !x. f x = g x |- f = g                 *)
      (list_eq_trans_rule
         [ (*               |- f = (\x. f x)      *)
           eq_sym_rule (eta_conv `\x. (f:'a->'b) x`);
           (* !x. f x = g x |- ... = (\x. g x)    *)
           mk_abs_rule x
             (spec_rule x (assume_rule `!x. (f:'a->'b) x = g x`));
           (*               |- ... = g            *)
           eta_conv `\x. (g:'a->'b) x` ])
      (* f = g |- !x. f x = g x                 *)
      (gen_rule x
        (mk_comb1_rule (assume_rule `(f:'a->'b)=g`) x) )))
);;


(* imp_alt_def_thm : thm                                                      *)
(*                                                                            *)
(*    |- $==> = (\p q. p /\ q <=> p)                                          *)

let imp_alt_def_thm = save_thm ("imp_alt_def_thm",
  let th1 = assume_rule p in
  eq_trans_rule
    (eq_sym_rule
      (eq_trans_rule
        (mk_abs_rule p (eta_conv `\q. $==> p q`))
        (eta_conv `\p. $==> p`) ))
    (foldr mk_abs_rule [p;q]
      (* |- p ==> q <=> (p /\ q <=> p)        *)
      (deduct_antisym_rule
        (* p /\ q <=> p |- p ==> q              *)
        (disch_rule p
          (conjunct2_rule
            (* p /\ q <=> p, p |- p /\ q            *)
            (undisch_rule
              (eq_imp_rule2 (assume_rule `p /\ q <=> p`)) )))
        (* p ==> q |- p /\ q <=> p              *)
        (deduct_antisym_rule
          (* p ==> q |- p ==> p /\ q              *)
          (conj_rule th1
            (mp_rule (assume_rule `p ==> q`) th1) )
          (* p /\ q |- p                          *)
          (conjunct1_rule (assume_rule `p /\ q`)) )))
);;


end;;
