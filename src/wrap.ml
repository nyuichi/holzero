(* ========================================================================== *)
(* INFERENCE KERNEL WRAPPERS (HOL Zero)                                       *)
(* - Basic wrappers for the primitive inference rules and theory commands     *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2015                            *)
(* ========================================================================== *)


module Wrap : Wrap_sig = struct


(* The primitive inference rules and theory commands have minimal, stripped-  *)
(* down functionality, to make the language and inference kernels as concise  *)
(* as possible and their correctness as easy as possible to justify.  This    *)
(* module adds basic wrappers around these primitives, giving the rules step  *)
(* counting and the theory commands benign redefinition and slightly enhanced *)
(* functionality.                                                             *)


open Type;;
open Term;;
open Thm;;
open Utils1;;
open Utils2;;
open CoreThry;;



(* ** WRAPPED INFERENCE RULES ** *)

(* Counters are maintained for the absolute and relative numbers of           *)
(* successful primitive inference rule steps.                                 *)


(* Absolute counter *)

(* The absolute step counter is a simple total that cannot be reset.  It      *)
(* starts at 0 and is incremented with every successful execution of a        *)
(* primitive inference rule.                                                  *)

let the_absolute_step_total = ref 0;;

let step_total () = !the_absolute_step_total;;

let inc_step_total () =
  (the_absolute_step_total := !the_absolute_step_total + 1);;


(* Relative counter *)

(* The relative step counter counts the number of primitive inference steps   *)
(* from the point it is reset, by storing the absolute total at that point.   *)

let the_relative_step_start = ref 0;;

let reset_step_counter () =
  (the_relative_step_start := !the_absolute_step_total);;

let step_counter () = !the_absolute_step_total - !the_relative_step_start;;


(* The wrapped versions of the primitive inference rules have exactly the     *)
(* same behaviour as their primitive counterparts, except that they increment *)
(* the absolute step counter for a successful execution.                      *)

let eq_refl_conv tm =
  let th' = prim_eq_refl_conv tm in
  (inc_step_total ();
   th');;

let beta_conv tm =
  let th' = try2 prim_beta_conv tm   "beta_conv" in
  (inc_step_total ();
   th');;

let mk_comb_rule th1 th2 =
  let th' = try2 (prim_mk_comb_rule th1) th2   "mk_comb_rule" in
  (inc_step_total ();
   th');;

let mk_abs_rule v th =
  let th' = try2 (prim_mk_abs_rule v) th   "mk_abs_rule" in
  (inc_step_total ();
   th');;

let assume_rule tm =
  let th' = try2 prim_assume_rule tm   "assume_rule" in
  (inc_step_total ();
   th');;

let disch_rule tm th =
  let th' = try2 (prim_disch_rule tm) th   "disch_rule" in
  (inc_step_total ();
   th');;

let mp_rule th1 th2 =
  let th' = try2 (prim_mp_rule th1) th2   "mp_rule" in
  (inc_step_total ();
   th');;

let eq_mp_rule th1 th2 =
  let th' = try2 (prim_eq_mp_rule th1) th2   "eq_mp_rule" in
  (inc_step_total ();
   th');;

let inst_rule theta th =
  let th' = try2 (prim_inst_rule theta) th   "inst_rule" in
  (inc_step_total ();
   th');;

let inst_type_rule tytheta th =
  let th' = try2 (prim_inst_type_rule tytheta) th   "inst_type_rule" in
  (inc_step_total ();
   th');;



(* ** WRAPPED THEORY COMMANDS ** *)

(* The wrapped theory commands add benign redefinition to their unwrapped     *)
(* counterparts.  This allows the user to resubmit the same proof script      *)
(* command in the same HOL Zero session without causing an error.             *)


(* Type constant database retrieval *)

(* The wrapped retrieval commands for the type constant database return type  *)
(* constant arity as an OCaml 'int' integer, instead of the 'big_int' integer *)
(* returned by the primitive commands.                                        *)

let get_tyconst_arity x =
  let n = try2 prim_get_tyconst_arity x    "get_tyconst_arity" in
  if (is_int_big_int n)
    then int_of_big_int n
    else hol_fail ("get_tyconst_arity", "Not a small-integer arity");;

let get_all_tyconsts () =
  let xns = try2 prim_get_all_tyconsts ()   "get_all_tyconsts" in
  if (forall (is_int_big_int <* snd) xns)
    then snd_map int_of_big_int xns
    else let (x,_) = find (not <* is_int_big_int <* snd) xns in
         hol_fail ("get_all_tyconsts",
                  "Type constant " ^ x ^ " does not have small-integer arity");;


(* Type constant declaration *)

(* The wrapper for type constant declaration returns a general instance of    *)
(* the declared type constant, as well as catering for benign redefinition.   *)
(* It takes an OCaml 'int' integer for the type constant arity, instead of    *)
(* the 'big_int' inteter taken by the primitive command.                      *)

(* new_tyconst : string * int -> hol_type                                     *)
(*                                                                            *)
(* This is the type constant declaration command.  It takes a string and an   *)
(* integer.  The string becomes the name of a new type constant in the        *)
(* theory, and the integer becomes its arity.  Any name can be used for a     *)
(* type constant, but supplying an existing type constant's name will cause   *)
(* failure (unless the arity is the same as the existing one's, in which case *)
(* it's recognised as benign redeclaration and allowed).  A note of the       *)
(* declaration is reported, and a general instance of the new type constant,  *)
(* with numbered tyvars for its type parameters, is returned.                 *)

let ntyvars n = map (fun i -> mk_var_type (string_of_int i)) (up_to 1 n);;

let new_tyconst (x,n) =
  let n' = big_int_of_int n in
  try
    (prim_new_tyconst (x,n');
     mk_comp_type (x, ntyvars n))
  with HolFail (_,msg) -> try
    (* Benign redefinition *)
    let n0' = prim_get_tyconst_arity x in
    let () = assert0 (eq_big_int n' n0')    LocalFail in
    (warn ("Benign redeclaration of type constant " ^ quote x);
     mk_comp_type (x, ntyvars n))
  with HolFail _ | LocalFail -> raise (HolFail ("new_tyconst",msg));;


(* Constant declaration *)

(* The wrapper for type constant declaration returns a general instance of    *)
(* the declared constant, as well as catering for benign redefinition.        *)

(* new_const : string * hol_type -> term                                      *)
(*                                                                            *)
(* This is the constant declaration command.  It takes a string and a type.   *)
(* The string becomes the name of a new constant in the theory, and the type  *)
(* becomes its generic type.  Any name can be used for a constant, but        *)
(* supplying an existing constant's name will cause failure (unless the       *)
(* generic type is the same as the existing one's, in which case it is        *)
(* recognised as benign redeclaration and allowed).  A note of the            *)
(* declaration is reported, and an instance of the new constant with its      *)
(* generic type is returned.                                                  *)

let new_const (x,ty) =
  try
    (prim_new_const (x,ty);
     mk_iconst (x,[]))
  with HolFail (_,msg) -> try
    (* Benign redefinition *)
    let ty0 = get_const_gtype x in
    let () = assert0 (ty = ty0)    LocalFail in
    (warn ("Benign redeclaration of constant " ^ quote x);
     mk_iconst (x,[]))
  with HolFail _ | LocalFail -> raise (HolFail ("new_const",msg));;


(* Axiom assertion *)

(* The wrapper for axiom assertion simply adds support for benign             *)
(* redefinition.                                                              *)

(* new_axiom : string * term -> thm                                           *)
(*                                                                            *)
(* This is the axiom assertion command.  It takes a string and a term.  The   *)
(* string becomes the name of a new axiom in the theory, and must not be an   *)
(* existing axiom name (unless in benign redefinition).  The term becomes the *)
(* asserted axiom, and must be of boolean type and must not contain free      *)
(* variables.  The resulting assertion theorem states that the supplied       *)
(* boolean term holds, under no assumptions.  A note of the axiom is          *)
(* reported, and the assertion theorem is returned.                           *)
(*                                                                            *)
(*    `p`      [ no free vars in `p` ]                                        *)
(*    ----                                                                    *)
(*    |- p                                                                    *)

let new_axiom (x,tm) =
  try
    prim_new_axiom (x,tm)
  with HolFail (_,msg) -> try
    (* Benign redefinition *)
    let th0 = get_axiom x in
    let () = assert0 (alpha_eq tm (concl th0))    LocalFail in
    (warn ("Benign redefinition of axiom " ^ quote x);
     th0)
  with HolFail _ | LocalFail -> raise (HolFail ("new_axiom",msg));;


(* Constant definition *)

(* As well as catering for benign redefinition, the wrapped form of constant  *)
(* definition takes its input as a single equality term, with the new         *)
(* constant (or actually a placeholder for it) as the LHS, and its value as   *)
(* the RHS.                                                                   *)

(* new_const_definition : term -> thm                                         *)
(*                                                                            *)
(* This is the constant definition command.  It takes an equality term        *)
(* argument.  The LHS of the equality must be a variable which must not have  *)
(* the name of an existing constant (unless in benign redefinition), and the  *)
(* RHS must not contain any free variables.  The resulting theorem defines a  *)
(* new constant with the same name as the variable in the input LHS.  It has  *)
(* no assumptions and a conclusion that states the constant is equal to the   *)
(* input RHS.                                                                 *)
(*                                                                            *)
(*    `%c = t`       [ no free vars in `t`;                                   *)
(*    --------         any tyvars in `t` must occur in type of `t` ]          *)
(*    |- c = t                                                                *)

let new_const_definition tm =                (* c = t     *)
  let func = "new_const_definition" in
  let (lhs,rhs) = try1 dest_eq tm        (func,"Term is not an equality") in
  let x = try var_name lhs  with HolFail _ ->
          try const_name lhs  with HolFail _ ->
                                         hol_fail (func,"LHS is not a var") in
  try
    prim_new_const_definition (x,rhs)
  with HolFail (_,msg) -> try
    (* Benign redefinition *)
    let th0 = get_const_definition x in
    let rhs0 = eqthm_rhs th0 in
    let () = assert0 (alpha_eq rhs rhs0)    LocalFail in
    (warn ("Benign redefinition of constant " ^ quote x);
     th0)
  with HolFail _ | LocalFail -> raise (HolFail (func,msg));;


(* Constant specification *)

(* The wrapped form of constant specification caters for benign redefinition. *)

(* new_const_specification : string list * thm -> thm                         *)
(*                                                                            *)
(* This is the primitive specification command for constants.  It takes a     *)
(* non-empty string list and an existentially quantified theorem.  The        *)
(* strings correspond one-to-one to the names of the new constants to be      *)
(* added to the theory, and must not include any existing constant names      *)
(* (unless in benign redefinition).  They also correspond one-to-one to the   *)
(* outer-quantified variables of the supplied existential theorem, in the     *)
(* same order, although they potentially have different names.  The supplied  *)
(* existential theorem must have no free variables and no assumptions.        *)
(* Furthermore, its outer-quantified variables must each have the same type   *)
(* variables, and the body of the existential must not involve any other type *)
(* variables.                                                                 *)
(*                                                                            *)
(* The resulting definition theorem states that the body of the existential   *)
(* is satisfied for the new constants, where the constants replace the        *)
(* outermost quantified variables respectively according to the order in the  *)
(* string list, under no assumptions.                                         *)
(*                                                                            *)
(*    "c1" "c2" ..    |- ?x1 x2 .. . p   [ only "x1", "x2", .. free in `p` ]  *)
(*    --------------------------------                                        *)
(*           |- p[c1/x1;c2/x2;..]                                             *)

let new_const_specification (xs,th) =        (* |- ? v1 v2 .. . p    *)
  try
    prim_new_const_specification (xs,th)
  with HolFail (_,msg) -> try
    (* Benign respecification *)
    let ((xs0,th0),th1) = get_const_specification_info (hd xs) in
    let () = assert0 (xs = xs0)                           LocalFail in
    let () = assert0 (alpha_eq (concl th) (concl th0))    LocalFail in
    (warn ("Benign respecification of constant" ^
           (if (length xs > 1) then "s" else "") ^
           " " ^ foldl1 (fun y x -> y ^ ", " ^ quote x) xs);
     th0)
  with HolFail _ | LocalFail -> raise (HolFail("new_const_specification",msg));;


(* Type constant definition *)

(* As well as catering for benign redefinition, the wrapped form of type      *)
(* constant definition caters for transforming the inputted existential       *)
(* theorem if necessary to give an explicit characteristic function (by using *)
(* lambda abstraction).                                                       *)

(* new_tyconst_definition : string * thm -> thm                               *)
(*                                                                            *)
(* This is the type constant definition command.  It takes a string and a     *)
(* theorem.  The string becomes the name of the new type constant, and must   *)
(* not be the name of an existing type constant (unless in benign             *)
(* redefinition).  The theorem argument must have no assumptions and a        *)
(* conclusion of the form `?x. p`, where `\x. p` is the characteristic        *)
(* function (prescribing the subset of the representation type that is in     *)
(* bijection with a general instance of the new type constant), and the       *)
(* theorem itself establishes that the subset is non-empty.  The term `p`     *)
(* must not contain free variables other than "x", and its number of type     *)
(* variables becomes the arity of the new type constant.                      *)
(*                                                                            *)
(* The resulting definition theorem uses "TYPE_DEFINITION" to state that a    *)
(* bijection exists between a general instance of the new type constant and   *)
(* those elements of the representation type that satisfy `\x. p`, under no   *)
(* assumptions.                                                               *)
(*                                                                            *)
(*         "ty"     |- ?(x:ty0). p               [ no free vars in `p` other  *)
(*    -----------------------------------------    than "x" ]                 *)
(*    |- ?(f:ty->ty0). TYPE_DEFINITION (\x.p) f                               *)

let new_tyconst_definition (x,th) =
  let func = "new_tyconst_definition" in
  let (v,p) = try1 dest_exists (concl th)   (func, "Not of the form `?v. p`") in
  let th1 =
     if (is_comb p) &&
        (let (cf,v0) = dest_comb p in  (v0 = v) && not (var_free_in v cf))
       then th                         (* |- ?v. p             *)
       else let p0 = mk_comb (mk_abs (v,p), v) in
            let e = mk_iconst ("=", [(a_ty,bool_ty)]) in
            let ex = mk_iconst ("?", [(a_ty, type_of v)]) in
            let th1 = mk_comb_rule (eq_refl_conv ex)
                                   (mk_abs_rule v (beta_conv p0)) in
                                                (* |- ?v. (\v. p) v <=> ?v. p *)
            let th2 = eq_refl_conv (mk_exists (v,p0)) in
            eq_mp_rule
              (eq_mp_rule (mk_comb_rule (mk_comb_rule (eq_refl_conv e) th1) th2)
                          th2)
              th in                    (* |- ?v. (\v. p) v     *)
  try
    prim_new_tyconst_definition (x,th1)
  with HolFail (_,msg) -> try
    (* Benign redefinition *)
    let (th10,th0) = get_tyconst_definition_info x in
    let () = assert0 (thm_alpha_eq th10 th1)    LocalFail in
    (warn ("Benign redefinition of type constant " ^ quote x);
     th0)
  with HolFail _ | LocalFail -> raise (HolFail (func,msg));;


end;;
