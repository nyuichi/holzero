(* ========================================================================== *)
(* CORE THEORY (HOL Zero)                                                     *)
(* - A core theory for the HOL logic                                          *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2014                            *)
(* ========================================================================== *)


module CoreThry : CoreThry_sig = struct


(* This module completes the logical core for HOL by defining the core        *)
(* theory.  This involves giving declarations, definitions and axioms for all *)
(* the HOL theory entities anticipated by the language and inference kernels. *)

(* This module is part of the logical core and thus crucial to the soundness  *)
(* of the system.  However, strictly speaking this module is not a trusted    *)
(* component of the system, since any declarations and assertions made here   *)
(* are registered by the language and inference kernels respectively, and     *)
(* thus can be inspected by a proof auditor in a proof session.               *)

(* Note that, for clarity and ease of implementation, HOL quotations (as      *)
(* opposed to syntax constructor functions) are used to create types and      *)
(* terms, and so this module must be defined after the parser.                *)


open Type;;
open Term;;
open Thm;;

open Names;;
open Parser;;



(* ** DECLARED CONSTANTS AND TYPE CONSTANTS ** *)

(* The core theory starts with entities that are just declared instead of     *)
(* being defined, to give the first definitions something to be defined in    *)
(* terms of.  There are 5 such declared entities in HOL Zero: 2 type          *)
(* constants and 3 constants.  Their meaning arises from the primitive        *)
(* inference rules and the core theory axioms.                                *)


(* Function types *)

(* First is the function type operator, for representing the type of          *)
(* functions, which are fundamental to primitive HOL language.  Function      *)
(* types have two parameters: a domain type and a range type.  This is the    *)
(* only theory entity anticipated by the language kernel.                     *)

let () = set_type_fixity ("->", Infix (5,RightAssoc));;

let () = prim_new_tyconst ("->", big_int_2);;


(* Boolean type *)

(* Next is the boolean base type, for representing the classic boolean values *)
(* (i.e. "true" and "false").  This is fundamental to the inference kernel    *)
(* and its notion of a theorem.                                               *)

let () = prim_new_tyconst ("bool", big_int_0);;

let bool_ty = mk_comp_type ("bool",[]);;


(* Equality *)

(* The equality function represents classic mathematical equality.            *)

let () = set_fixity ("=", Infix (30,NonAssoc));;

let () = prim_new_const ("=", `:'a->'a->bool`);;


(* Implication *)

(* The implication function represents the classic implication operator in    *)
(* propositional logic.                                                       *)

let () = set_fixity ("==>", Infix (10,RightAssoc));;

let () = prim_new_const ("==>", `:bool->bool->bool`);;


(* Selection *)

(* The selection operator represents the Hilbert Choice operator, which       *)
(* selects an element of a given type, depending on a supplied predicate over *)
(* elements of the type.  When there is at least one element that satisfies   *)
(* the predicate, it selects one such element, and when no elements satisfy   *)
(* the predicate, it selects an arbitrary element of the type.                *)

let () = set_fixity ("@", Binder);;

let () = prim_new_const ("@", `:('a->bool)->'a`);;


(* Logical equivalence *)

(* Logical equivalence is written using "<=>", which is actually just an      *)
(* alias for equality over the boolean type.  The name is given infix status  *)
(* and declared as a dummy constant here (the constant is never able to occur *)
(* in the actual internal representation of a term).  This hack is done to    *)
(* enable the parser/printer to cater for logical equivalence without general *)
(* support for aliases, and to prevent "<=>" from being declared a constant   *)
(* by the user.                                                               *)

let () = set_fixity ("<=>", Infix (5,NonAssoc));;

let () = prim_new_const ("<=>", `:bool->bool->bool`);;



(* ** DEFINED CONSTANTS ** *)

(* The remaining 6 constants that occur in the logical core are built up in a *)
(* succession of basic definitions that are expressed in terms of existing    *)
(* constants and type constants.                                              *)


(* Truth *)

(* Truth is synonymous with statements that hold in the logic, and so it must *)
(* be defined to be some value that is intended to universally hold.  As for  *)
(* any constant definition, this term value cannot involve free variables.    *)
(* Neither can it involve type variables, because truth is of type boolean,   *)
(* which is not polymorphic.  The term used here just uses equality and the   *)
(* boolean type.  It is the instance of the equality reflexive property for   *)
(* the boolean identity function.                                             *)

let true_def =
  prim_new_const_definition ("true", `(\(p:bool). p) = (\p. p)`);;

let true_tm = `true`;;


(* Universal quantifier *)

(* The universal quantifier is defined using equality and truth, simply as    *)
(* the function that returns whether its predicate argument returns true for  *)
(* every input.                                                               *)

let () = set_fixity ("!", Binder);;

let forall_def =
  prim_new_const_definition ("!", `\(P:'a->bool). P = (\x. true)`);;


(* Conjunction *)

(* Conjunction is defined here using implication and the universal            *)
(* quantifier, as the binary function that returns whether, for any boolean   *)
(* value, the arguments together implying the value necessarily implies the   *)
(* value.                                                                     *)

let () = set_fixity ("/\\", Infix (20,RightAssoc));;

let conj_def =
  prim_new_const_definition ("/\\", `\p1 p2. !p. (p1 ==> (p2 ==> p)) ==> p`);;


(* Existential quantifier *)

(* The existential quantifier is defined using just selection, as the         *)
(* function that returns whether any element selected as satisfying the       *)
(* function's predicate argument necessarily satisfies the predicate.  Note   *)
(* that if there is no element satisfying the predicate, then not even the    *)
(* result of the selection operation can satisfy the predicate.               *)

let () = set_fixity ("?", Binder);;

let exists_def =
  prim_new_const_definition ("?", `\(P:'a->bool). P ($@ P)`);;


(* One-to-one predicate *)

(* The one-to-one predicate is defined as the function that returns whether   *)
(* its function argument having the same result when applied to two elements  *)
(* necessarily implies that the two elements are equal.                       *)

let one_one_def =
  prim_new_const_definition
    ("ONE_ONE", `\(f:'a->'b). !x1 x2. f x1 = f x2 ==> x1 = x2`);;


(* Type definition predicate *)

(* This predicate is used in the theorem created by the primitive type        *)
(* constant definition command to assert that there is a bijection from the   *)
(* new type to its representation type.  It is defined as the function that   *)
(* takes a characteristic function (a predicate for elements of the           *)
(* representation type) and a representation function (mapping elements of    *)
(* the new type to the representation type), and returns whether the          *)
(* representation function is one-to-one and maps onto precisely those        *)
(* elements in the representation type that satisfy the characteristic        *)
(* function.                                                                  *)

let type_definition_def =
  prim_new_const_definition
    ("TYPE_DEFINITION",
     `\P (rep:'b->'a). ONE_ONE rep /\ (!x. P x <=> (?y. x = rep y))`);;



(* ** AXIOMS ** *)

(* It is sufficient to give 3 axioms to complete the core theory.             *)


(* Eta Axiom *)

(* This axiom states that, for any given function, the lambda abstraction     *)
(* formed by applying the function to the binding variable is equal to the    *)
(* function.                                                                  *)

let eta_ax =
  prim_new_axiom ("eta_ax", `!(f:'a->'b). (\x. f x) = f`);;


(* Implication Antisymmetry Axiom *)

(* This axiom states the antisymmetry property for implication.               *)

let imp_antisym_ax =
  prim_new_axiom ("imp_antisym_ax",
                  `!p1 p2. (p1 ==> p2) ==> ((p2 ==> p1) ==> (p1 <=> p2))`);;


(* Axiom of Choice *)

(* This axiom states a crucial property about the selection operator, namely  *)
(* that any element satisfying a given predicate implies that the selected    *)
(* element for the predicate satisfies the predicate.  Note that it says      *)
(* nothing about when there is no element that can satisfy the predicate.     *)

let select_ax =
  prim_new_axiom ("select_ax", `!(P:'a->bool) x. P x ==> P ($@ P)`);;


end;;
