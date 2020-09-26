(* ========================================================================== *)
(* INFERENCE KERNEL (HOL Zero)                                                *)
(* - Datatype for internal theorems plus primitive inference and assertion    *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2015                            *)
(* ========================================================================== *)


module Thm : Thm_sig = struct


(* This module defines the basic mechanisms for logical deduction and theory  *)
(* assertion.  As is characteristic of LCF-style theorem provers, this is     *)
(* done by defining an abstract datatype for the internal representation of   *)
(* theorems.  The primitive constructors for this datatype are limited to the *)
(* primitive inference rules and the primitive assertion commands.  Any       *)
(* subsequent theorem-creating functions must ultimately be implemented in    *)
(* terms of these constructors.  This module is a trusted component of the    *)
(* system.                                                                    *)

(* Note that the primitive constructors are defined here in anticipation of   *)
(* suitable declarations/definitions of certain HOL theory entities.  These   *)
(* entities are introduced in the module 'CoreThry', and the logcial core is  *)
(* not fully defined until this has been processed.                           *)

(* The 'immutise' function is used wherever string inputs/outputs set/return  *)
(* internal string values, to avoid OCaml string mutability problems (see     *)
(* 'system.ml').                                                              *)


open DLTree;;

open Type;;
open Term;;

open Utils1;;



(* ** THEOREM DATATYPE ** *)


(* thm *)

(* This is the datatype for internal HOL theorems.  A theorem consists of a   *)
(* list of assumptions and a conclusion, all of which are boolean terms.      *)

type thm = Theorem of term list * term;;


(* Destructors *)

let dest_thm (Theorem (hs,c)) = (hs,c);;

let asms th = fst (dest_thm th);;
let concl th = snd (dest_thm th);;


(* Equality *)

let thm_eq x y = (Pervasives.compare x y = 0);;



(* ** PRIMITIVE INFERENCE RULES ** *)

(* There are 10 primitive inference rules.  These give basic properties about *)
(* equality, lambda abstraction, propositional deduction and instantiation,   *)
(* and correspond to classic rules of typed lambda calculus and propositional *)
(* logic.  All of these rules work modulo alpha-equivalence.                  *)


(* prim_eq_refl_conv : term -> thm                                            *)
(*                                                                            *)
(* This is the reflexivity rule for equality.  It takes a term, and returns a *)
(* theorem stating that this term is equal to itself, under no assumptions.   *)
(* There are no restrictions on the supplied term.                            *)
(*                                                                            *)
(*       `t`                                                                  *)
(*    --------                                                                *)
(*    |- t = t                                                                *)

let prim_eq_refl_conv tm =
  let c' = mk_eq (tm,tm) in
  Theorem ([],c');;


(* prim_beta_conv : term -> thm                                               *)
(*                                                                            *)
(* This is the beta reduction conversion.  It takes a lambda abstraction      *)
(* application term, and returns a theorem stating that the application is    *)
(* equal to the lambda abstraction body but with all occurrences of the       *)
(* binding variable replaced with the application's argument, under no        *)
(* assumptions.                                                               *)
(*                                                                            *)
(*         `(\x. t) s`                                                        *)
(*    ---------------------                                                   *)
(*    |- (\x. t) s = t[s/x]                                                   *)

let prim_beta_conv tm =
  let func = "prim_beta_conv" in
  let (f,tm2) = try1 dest_comb tm   (func,"Not a function application term") in
  let (v,tm1) = try1 dest_abs f
                       (func,"Function subterm is not a lambda abstraction") in
  let c' = mk_eq (tm, var_inst [(v,tm2)] tm1) in
  Theorem ([],c');;


(* prim_mk_comb_rule : thm -> thm -> thm                                      *)
(*                                                                            *)
(* This is the equality congruence rule for function application.  It takes   *)
(* two equality theorems, and applies corresponding sides of the first        *)
(* theorem to the second, unioning the assumptions.  The first theorem's LHS/ *)
(* RHS must be functions with domain type equal to the type of the second     *)
(* theorem's LHS/RHS.                                                         *)
(*                                                                            *)
(*    A1 |- f1 = f2    A2 |- t1 = t2                                          *)
(*    ------------------------------                                          *)
(*       A1 u A2 |- f1 t1 = f2 t2                                             *)

let prim_mk_comb_rule (Theorem (hs1,c1)) (Theorem (hs2,c2)) =
  let func = "prim_mk_comb_rule" in
  let (lhs1,rhs1) = try1 dest_eq c1    (func,"Arg 1 not an equality theorem") in
  let (lhs2,rhs2) = try1 dest_eq c2    (func,"Arg 2 not an equality theorem") in
  let hs' = union' alpha_eq hs1 hs2 in
  let c' = try mk_eq (mk_comb (lhs1,lhs2), mk_comb (rhs1,rhs2))
           with HolFail _ ->
           if (is_fun_type (type_of lhs1))
             then hol_fail
                      (func,"Function domain type not equal to argument type")
             else hol_fail (func,"Arg 1 not an equality between functions") in
  Theorem (hs',c');;


(* prim_mk_abs_rule : term -> thm -> thm                                      *)
(*                                                                            *)
(* This is the equality congruence rule for lambda abstraction.  It takes a   *)
(* variable and an equality theorem, and abstracts the variable from both     *)
(* sides of the theorem.  The variable must not occur free in the assumptions *)
(* of the supplied theorem.                                                   *)
(*                                                                            *)
(*       `x`   A |- t1 = t2        [ "x" not free in 'A' ]                    *)
(*    ------------------------                                                *)
(*    A |- (\x. t1) = (\x. t2)                                                *)

let prim_mk_abs_rule v (Theorem (hs,c)) =
  let func = "prim_mk_abs_rule" in
  let () = assert1 (is_var v)          (func,"Arg 1 not a variable") in
  let (lhs,rhs) = try1 dest_eq c       (func,"Arg 2 not an equality theorem") in
  let () = assert1 (not (exists (var_free_in v) hs))
                               (func,"Supplied variable occurs free in asms") in
  let c' = mk_eq (mk_abs (v,lhs), mk_abs (v,rhs)) in
  Theorem (hs,c');;


(* prim_assume_rule : term -> thm                                             *)
(*                                                                            *)
(* This is the assumption rule.  It takes a boolean term, and returns a       *)
(* theorem stating that the term holds under the single assumption of the     *)
(* term itself.                                                               *)
(*                                                                            *)
(*       `p`                                                                  *)
(*    --------                                                                *)
(*    {p} |- p                                                                *)

let prim_assume_rule tm =
  let () = assert1 (is_bool_term tm) ("prim_assume_rule","Not a boolean term")in
  Theorem ([tm],tm);;


(* prim_disch_rule : term -> thm -> thm                                       *)
(*                                                                            *)
(* This is the implication introduction rule.  It takes a boolean term and a  *)
(* theorem, and removes the term from the theorem's assumptions (if present)  *)
(* and adds it as an antecedent of the conclusion.  Note that the term does   *)
(* not have to be in the assumptions of the supplied theorem for the rule to  *)
(* succeed.                                                                   *)
(*                                                                            *)
(*      `p`   A |- q                                                          *)
(*    ----------------                                                        *)
(*    A\{p} |- p ==> q                                                        *)

let prim_disch_rule tm (Theorem (hs,c)) =
  let () = assert1 (is_bool_term tm)
                            ("prim_disch_rule","Arg 1 not a boolean term") in
  let hs' = subtract' alpha_eq hs [tm] in
  let c' = mk_imp (tm,c) in
  Theorem (hs',c');;


(* prim_mp_rule : thm -> thm -> thm                                           *)
(*                                                                            *)
(* This is the modus ponens rule.  It takes an implication theorem and a      *)
(* second theorem, where the implication theorem's antecedent is alpha-       *)
(* equivalent to the conclusion of the second theorem.  It returns a theorem  *)
(* stating that the implication theorem's consequent holds, under the unioned *)
(* assumptions of the supplied theorems.                                      *)
(*                                                                            *)
(*    A1 |- p ==> q    A2 |- p                                                *)
(*    ------------------------                                                *)
(*          A1 u A2 |- q                                                      *)

let prim_mp_rule (Theorem (hs1,c1)) (Theorem (hs2,c2)) =
  let func = "prim_mp_rule" in
  let (lhs,rhs) = try1 dest_imp c1  (func,"Arg 1 not an implication theorem") in
  let () = assert1 (alpha_eq lhs c2)
              (func,"Implication thm LHS not alpha-equivalent to 2nd thm") in
  let hs' = union' alpha_eq hs1 hs2 in
  Theorem (hs',rhs);;


(* prim_eq_mp_rule : thm -> thm -> thm                                        *)
(*                                                                            *)
(* This is the equality modus ponens rule.  It takes an equality theorem and  *)
(* a second theorem, where the equality theorem's LHS is alpha-equivalent to  *)
(* the conclusion of the second theorem.  It returns a theorem stating that   *)
(* the equality theorem's RHS holds, under the unioned assumptions of the     *)
(* supplied theorems.                                                         *)
(*                                                                            *)
(*    A1 |- p <=> q    A2 |- p                                                *)
(*    ------------------------                                                *)
(*          A1 u A2 |- q                                                      *)

let prim_eq_mp_rule (Theorem (hs1,c1)) (Theorem (hs2,c2)) =
  let func = "prim_eq_mp_rule" in
  let (lhs,rhs) = try1 dest_eq c1     (func,"Arg 1 not an equality theorem") in
  let () = assert1 (alpha_eq lhs c2)
                   (func,"Equality thm LHS not alpha-equivalent to 2nd thm") in
  let hs' = union' alpha_eq hs1 hs2 in
  Theorem (hs',rhs);;


(* prim_inst_rule : (term * term) list -> thm -> thm                          *)
(*                                                                            *)
(* This is the variable instantiation rule.  It takes a variable              *)
(* instantiation list and a theorem, and performs a single parallel           *)
(* instantiation of the free variables in the theorem's assumptions and       *)
(* conclusion, according to the instantiation list.  All free occurrences of  *)
(* instantiation list domain elements in the theorem get replaced.  Each      *)
(* instantiation list domain element must be a variable, and each range       *)
(* element must have the same type as its corresponding domain element.       *)
(*                                                                            *)
(* Binding variables in the resulting theorem are renamed as necessary to     *)
(* avoid variable capture.  Note that instantiation list entries that do not  *)
(* apply are simply ignored, as are repeated entries for a given variable     *)
(* (beyond its first entry).  If no instantiation list entries apply, then    *)
(* the returned theorem is the same as the input.                             *)
(*                                                                            *)
(*        [(x1,t1);(x2,t2);..]    A |- p                                      *)
(*    --------------------------------------                                  *)
(*    A[t1/x1,t2/x2,..] |- p[t1/x1,t2/x2,..]                                  *)

let prim_inst_rule theta (Theorem (hs,c)) =
  let c' = try2 (var_inst theta) c         "prim_inst_rule" in
  let hs' = setify' alpha_eq (map (var_inst theta) hs) in
  Theorem (hs',c');;


(* prim_inst_type_rule : (hol_type * hol_type) list -> thm -> thm             *)
(*                                                                            *)
(* This is the type variable instantiation rule.  It takes a type variable    *)
(* instantiation list and a theorem, and performs a single parallel           *)
(* instantiation of the type variables in the theorem's assumptions and       *)
(* conclusion, according to the instantiation list.  All occurrences of       *)
(* instantiation list domain elements in the theorem get replaced.  Each      *)
(* instantiation list domain element must be a type variable.                 *)
(*                                                                            *)
(* Binding variables in the resulting theorem are renamed as necessary to     *)
(* avoid variable capture.  Note that instantiation list entries that do not  *)
(* apply are simply ignored, as are repeated entries for a given type         *)
(* variable (beyond its first entry).  If no instantiation list entries       *)
(* apply, then the returned theorem is the same as the input.                 *)
(*                                                                            *)
(*         [(tv1,ty1);(tv2,ty2);..]    A |- p                                 *)
(*    ----------------------------------------------                          *)
(*    A[ty1/tv1,ty2/tv2,..] |- p[ty1/tv1,ty2/tv2,..]                          *)

let prim_inst_type_rule tytheta (Theorem (hs,c)) =
  let c' = try2 (tyvar_inst tytheta) c        "prim_inst_type_rule" in
  let hs' = setify' alpha_eq (map (tyvar_inst tytheta) hs) in
  Theorem (hs',c');;



(* ** PRIMITIVE ASSERTION COMMANDS ** *)

(* There are four primitive assertion commands, one for each of: introducing  *)
(* new axioms, defining new constants, specifying new constants and defining  *)
(* new type constants.                                                        *)

(* For each primitive assertion command, the resulting assertion theorem is   *)
(* registered in a database, and commands are provided for inspecting these   *)
(* databases.  A note that the assertion has taken place is reported, to      *)
(* ensure the user is kept aware of the change to the theory.                 *)


(* * AXIOM ASSERTION * *)

(* A boolean term can be asserted by introducing an axiom.  No restrictions   *)
(* are placed on the term other than that it cannot contain free variables.   *)
(* Axiom introduction can introduce inconsistency if not done carefully, and  *)
(* so should generally be avoided if the resulting theorem can be achieved by *)
(* other means.                                                               *)


(* Axiom database *)

(* Axioms are stored in a dynamic lookup tree, indexed by axiom name.         *)

let the_axioms = ref (dltree_empty : (string,thm) dltree);;


(* get_axiom : string -> thm                                                  *)
(*                                                                            *)
(* Returns the assertion theorem for the axiom with the supplied name.        *)

let get_axiom x =
 try
  dltree_lookup x !the_axioms
 with HolFail _ -> hol_fail ("get_axiom", "No axiom called " ^ quote x);;


(* get_all_axioms : unit -> (string * thm) list                               *)
(*                                                                            *)
(* Returns the name and assertion theorem for each asserted axiom.            *)

let get_all_axioms () =
  let xths = dltree_elems !the_axioms in
  fst_map immutise xths;;                               (* OCaml protection *)


(* Axiom assertion command *)

(* prim_new_axiom : string * term -> thm                                      *)
(*                                                                            *)
(* This is the primitive axiom assertion command.  It takes a string and a    *)
(* term.  The string becomes the name of a new axiom in the theory, and must  *)
(* not be an existing axiom name.  The term becomes the asserted axiom, and   *)
(* must be of boolean type and must not contain free variables.  The          *)
(* resulting assertion theorem states that the supplied boolean term holds,   *)
(* under no assumptions.  A note of the axiom is reported, and the assertion  *)
(* theorem is returned.                                                       *)
(*                                                                            *)
(*    `p`      [ no free vars in `p` ]                                        *)
(*    ----                                                                    *)
(*    |- p                                                                    *)

let prim_new_axiom (x,tm) =
  let func = "prim_new_axiom" in
  let x_ = immutise x in                                (* OCaml protection *)
  let () = assert1 (is_bool_term tm)         (func,"Term arg not a boolean") in
  let () = assert1 (is_empty (free_vars tm))
                                  (func,"Free vars not allowed in term arg") in
  let () = assert1 (cannot get_axiom x_)
                          (func, "Axiom name " ^ quote x_ ^ " already used") in
  let th = Theorem ([],tm) in
  (report ("Adding axiom " ^ quote x_);
   the_axioms := dltree_insert (x_,th) !the_axioms;
   th);;


(* * DEFINITION OF CONSTANTS * *)

(* Constants can be defined using conservative extension, asserting equality  *)
(* of the new constant to an expression involving no free variables.          *)


(* Constant definition database *)

(* Constant definitions are stored in a dynamic lookup tree, indexed by the   *)
(* name of the constant defined.                                              *)

let the_const_defs = ref (dltree_empty : (string,thm) dltree);;


(* get_const_definition : string -> thm                                       *)
(*                                                                            *)
(* Returns the assertion theorem for the defined constant with the supplied   *)
(* name.                                                                      *)

let get_const_definition x =
 try
  dltree_lookup x !the_const_defs
 with HolFail _ ->
  let func = "get_const_definition" in
  let () = assert1 (is_const_name x) (func, "No constant called " ^ quote x) in
  hol_fail (func, "No definition for constant " ^ quote x);;


(* get_all_const_definitions : unit -> (string * thm) list                    *)
(*                                                                            *)
(* Returns the name and assertion theorem for each defined constant.          *)

let get_all_const_definitions () =
  let xths = dltree_elems !the_const_defs in
  fst_map immutise xths;;                               (* OCaml protection *)


(* Constant definition command *)

(* prim_new_const_definition : string * term -> thm                           *)
(*                                                                            *)
(* This is the primitive definition command for constants.  It takes a string *)
(* and a term.  The string becomes the name of a new constant in the theory,  *)
(* and must not be the name of an existing constant.  The term determines the *)
(* value of the new constant, and must not contain free vars, and must not    *)
(* contain tyvars that are not in its top-level type.  The resulting          *)
(* definition theorem asserts that the new constant equals the supplied term, *)
(* under no assumptions.  A note of the definition is reported, and the       *)
(* definition theorem is returned.                                            *)
(*                                                                            *)
(*    "c"   `t`     [ no free vars in `t`;                                    *)
(*    ---------       any tyvars in `t` must occur in type of `t` ]           *)
(*    |- c = t                                                                *)

let prim_new_const_definition (x,tm) =
  let func = "prim_new_const_definition" in
  let x_ = immutise x in                                (* OCaml protection *)
  let ty = type_of tm in
  let () = assert1 (is_empty (free_vars tm))
                    (func,"Free vars not allowed in definition term") in
  let () = assert1 (subset' type_eq (term_tyvars tm) (type_tyvars ty))
                    (func,"Definition term contains tyvars not at top level") in
  let () = try2  prim_new_const (x_,ty)    func in
  let c = mk_gconst x_ in
  let th = Theorem ([], mk_eq (c,tm)) in
  (report ("Adding definition for constant " ^ quote x_);
   the_const_defs := dltree_insert (x_,th) !the_const_defs;
   th);;


(* * SPECIFICATION OF CONSTANTS * *)

(* A group of constants can be specified together by conservative extension,  *)
(* by supplying an existential theorem that establishes that values for the   *)
(* new constants exist that satisfy the existential body predicate.           *)


(* Constant specification database *)

(* Constant specifications are stored in a dynamic lookup tree, indexed by    *)
(* the name lists of the constants defined.  A lookup tree for the name list  *)
(* index in which a given constant name occurs is also maintained.            *)

let the_const_specs = ref (dltree_empty : (string list, (thm * thm)) dltree);;

let the_const_spec_names = ref (dltree_empty : (string, string list) dltree);;

let get_const_specification_info x =
  let func = "get_const_specification_info" in
 try
  let xs = dltree_lookup x !the_const_spec_names in
  let (xs,(th0,th1)) = dltree_elem xs !the_const_specs in
  ((map immutise xs, th0), th1)                         (* OCaml protection *)
 with HolFail _ ->
  if (is_const_name x)
    then hol_fail (func, "No specification for constant " ^ quote x)
    else hol_fail (func, "No constant called " ^ quote x);;

let get_all_const_specification_info () =
  let xtts = dltree_elems !the_const_specs in
  let xtts1 = map (fun (xs,(th0,th)) -> ((xs,th0),th)) xtts in
  fst_map (fun (xs_,th0) -> (map immutise xs_, th0))    (* OCaml protection *)
          xtts1;;                                       (* OCaml protection *)


(* get_const_specification : string -> thm                                    *)
(*                                                                            *)
(* Returns the assertion theorem for the specified constant with the supplied *)
(* name.                                                                      *)

let get_const_specification x =
  try2  snd (get_const_specification_info x)  "get_const_specification";;


(* get_all_const_specifications : unit -> (string list * thm) list            *)
(*                                                                            *)
(* Returns the constant names and assertion theorem for each group of         *)
(* specified constants.                                                       *)

let get_all_const_specifications () =
  try2  (fst_map fst) (get_all_const_specification_info ())
        "get_all_const_specifications";;


(* Constant specification command *)

(* prim_new_const_specification : string list * thm -> thm                    *)
(*                                                                            *)
(* This is the primitive specification command for constants.  It takes a     *)
(* non-empty string list and an existentially quantified theorem.  The        *)
(* strings correspond one-to-one to the names of the new constants to be      *)
(* added to the theory, and must not include any existing constant names.     *)
(* They also correspond one-to-one to the outer-quantified variables of the   *)
(* supplied existential theorem, in the same order, although they potentially *)
(* have different names.  The supplied existential theorem must have no free  *)
(* variables and no assumptions.  Furthermore, its outer-quantified variables *)
(* must each have the same type variables, and the body of the existential    *)
(* must not involve any other type variables.                                 *)
(*                                                                            *)
(* The resulting definition theorem states that the body of the existential   *)
(* is satisfied for the new constants, where the constants replace the        *)
(* outermost quantified variables respectively according to the order in the  *)
(* string list, under no assumptions.                                         *)
(*                                                                            *)
(*    "c1" "c2" ..    |- ?x1 x2 .. . p   [ only "x1", "x2", .. free in `p` ]  *)
(*    --------------------------------                                        *)
(*           |- p[c1/x1;c2/x2;..]                                             *)

let prim_new_const_specification (xs,th) =        (* |- ? v1 v2 .. . p    *)
  let func = "prim_new_const_specification" in
  let xs_ = map immutise xs in                          (* OCaml protection *)
  let (hs,c) = dest_thm th in
  let (vs0,tm0) = strip_exists c in
  let () = assert1 (is_empty hs)            (func,"Assumptions not allowed") in
  let () = assert1 (is_empty (free_vars c)) (func,"Free vars in conclusion") in
  let () = assert1 (is_nonempty xs_)    (func,"Name list must be non-empty") in
  let (vs,vs1) = try1 (cut_big_int (length_big_int xs_)) vs0
                         (func,"Name list longer than existential var list") in
  let () = assert1 (no_dups xs_)             (func,"Name list not distinct") in
  let tm1 = list_mk_exists (vs1,tm0) in
  let tyvs1 = term_tyvars tm1 in
  let (tyvs,tyvss) = hd_tl (map term_tyvars vs) in
  let () = assert1 (forall (set_eq' type_eq tyvs) tyvss)
                   (func,"Each outer-existential var must have same tyvars") in
  let () = assert1 (subset' type_eq tyvs1 tyvs)
                   (func,"Existential body contains tyvars not in var list") in
  let _ = try assert (forall (not <* is_const_name) xs_)
          with Assert_failure _ ->
               let x = find is_const_name xs_ in
               hol_fail (func, "Constant name " ^ quote x ^ " already used") in
  let tys = map type_of vs in
  let () = do_map prim_new_const (zip xs_ tys) in
  let cs = map mk_gconst xs_ in
  let theta = zip vs cs in
  let th1 = Theorem ([], var_inst theta tm1) in
  (report ("Adding specification for constant" ^
           (if (gt_big_int (length_big_int xs_) big_int_1) then "s" else "") ^
           " " ^ foldl1 (fun y_ x_ -> y_ ^ ", " ^ x_) (map quote xs_));
   the_const_specs := dltree_insert (xs_,(th,th1)) !the_const_specs;
   do_map (fun x_ -> the_const_spec_names :=
                          dltree_insert (x_,xs_) !the_const_spec_names)
          xs_;
   th1);;


(* * DEFINITION OF TYPE CONSTANTS * *)

(* Type constants can be defined by conservative extension, asserting the     *)
(* existence of a bijection from a general instance of the new type constant  *)
(* to a prescribed non-empty subset of an existing type (called the           *)
(* "representation type").  The subset is prescribed by a predicate on the    *)
(* representation type (called the "characteristic function"), and its non-   *)
(* emptiness is established by supplying an existential theorem stating that  *)
(* there exists an element satisfying this predicate.                         *)


(* Type constant definition database *)

(* Type constants definitions are stored in a dynamic lookup tree, indexed by *)
(* the name of the type constant defined.                                     *)

let the_tyconst_defs = ref (dltree_empty : (string, thm * thm) dltree);;

let get_tyconst_definition_info0 func x =
 try
  dltree_lookup x !the_tyconst_defs
 with HolFail _ ->
  let () = assert1 (is_tyconst_name x)
                           (func, "No type constant called " ^ quote x) in
  hol_fail (func, "No type definition for type constant " ^ quote x);;

let get_tyconst_definition_info x =
  get_tyconst_definition_info0 "get_tyconst_definition_info" x;;

let get_all_tyconst_definition_info () =
  let xthths = dltree_elems !the_tyconst_defs in
  fst_map immutise xthths;;                             (* OCaml protection *)


(* get_tyconst_definition : string -> thm                                     *)
(*                                                                            *)
(* Returns the assertion theorem for the defined type constant with the       *)
(* supplied name.                                                             *)

let get_tyconst_definition x =
  snd (get_tyconst_definition_info0 "get_tyconst_definition" x);;


(* get_all_tyconst_definitions : unit -> (string * thm) list                  *)
(*                                                                            *)
(* Returns the name and assertion theorem for each defined type constant.     *)

let get_all_tyconst_definitions () =
  let xthths = dltree_elems !the_tyconst_defs in
  let xths = map (fun (x,(th0,th)) -> (x,th)) xthths in
  fst_map immutise xths;;                               (* OCaml protection *)


(* Type constant definition command *)

(* prim_new_tyconst_definition : string * thm -> thm                          *)
(*                                                                            *)
(* This is the primitive definition command for type constants.  It takes a   *)
(* string and a theorem.  The string becomes the name of a new type constant  *)
(* in the theory, and must not be the name of an existing type constant.  The *)
(* theorem argument must have no assumptions and a conclusion of the form     *)
(* `?v. P v`, where `P` is the characteristic function (prescribing the       *)
(* subset of the representation type that is in bijection with a general      *)
(* instance of the new type constant), and the theorem itself establishes     *)
(* that the subset is non-empty.  The predicate `P` must not contain free     *)
(* variables, and its number of type variables becomes the arity of the new   *)
(* type constant.                                                             *)
(*                                                                            *)
(* The resulting definition theorem uses the "TYPE_DEFINITION" predicate (see *)
(* 'CoreThry' module) applied to `P` to assert that a bijection exists        *)
(* between a general instance of the new type constant and those elements of  *)
(* the representation type that satisfy `P`, under no assumptions.  The       *)
(* general instance of the new type constant in this theorem has type         *)
(* variable parameters corresponding to the type variables of `P` in          *)
(* alphabetical order.  A note of the definition is reported, and the         *)
(* definition theorem is returned.                                            *)
(*                                                                            *)
(*         "ty"     |- ?(x:ty0). P x           [ no free vars in `P` ]        *)
(*    ------------------------------------                                    *)
(*    |- ?(f:ty->ty0). TYPE_DEFINITION P f                                    *)

let prim_new_tyconst_definition (x, (Theorem (hs0,c0) as th0)) =
  let func = "prim_new_tyconst_definition" in
  let x_ = immutise x in                                (* OCaml protection *)
  let (v,pv) = try1 dest_exists c0     (func,"Thm arg must match `?x. P x`") in
  let (p,v1) = try1 dest_comb pv       (func,"Thm arg must match `?x. P x`") in
  let () = assert1 (term_eq v1 v)      (func,"Thm arg must match `?x. P x`") in
  let () = assert1 (is_empty hs0)      (func,"Asms not allowed in thm arg") in
  let () = assert1 (is_empty (free_vars p))
           (func,"Free vars not allowed in thm arg characteristic function") in
  let ty0 = type_of v in
  let tyvs = mergesort (type_lt) (term_tyvars p) in   (* sort alphabetically  *)
  let () = try2  prim_new_tyconst (x_, length_big_int tyvs)    func in
  let ty = mk_comp_type (x_,tyvs) in
  let f = mk_var ("f", mk_fun_type (ty,ty0)) in
  let tdef = mk_iconst ("TYPE_DEFINITION", [(a_ty,ty0);(b_ty,ty)]) in
  let th = Theorem ([], mk_exists (f, list_mk_comb (tdef,[p;f]))) in
  (report ("Adding definition for type constant " ^ quote x_);
   the_tyconst_defs := dltree_insert (x_,(th0,th)) !the_tyconst_defs;
   th);;


end;;
