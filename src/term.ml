(* ========================================================================== *)
(* TERMS (HOL Zero)                                                           *)
(* - Datatype for internal terms plus support for constant declaration        *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2013                            *)
(* ========================================================================== *)


module Term : Term_sig = struct


(* This module defines the internal representation of HOL terms.  This is     *)
(* done by defining an abstract datatype for terms, and then primitive syntax *)
(* functions for constructing and destructing terms, and support for constant *)
(* declaration.  The primitive syntax constructors ensure that only well-     *)
(* formed terms can be constructed.  This module is a trusted component of    *)
(* the system.                                                                *)

(* Also defined in this module is a primitive utility (for calculating the    *)
(* type of a term) that is needed in the definition of a primitive syntax     *)
(* function.                                                                  *)

(* The 'immutise' function is used wherever string inputs/outputs set/return  *)
(* internal string values, to avoid OCaml string mutability problems (see     *)
(* 'system.ml').                                                              *)


open DLTree;;

open Type;;



(* ** TERM DATATYPE ** *)


(* term *)

(* This is the datatype for internal HOL terms.  It has 4 classes,            *)
(* corresponding to the 4 primitive syntactic categories of term:             *)
(*                                                                            *)
(*   Variable - This denotes an occurrence of a variable.  It has name and    *)
(*  type attributes.  Any two occurrences of variables within a given object  *)
(*  refer the same entity iff they have the same name, type and scope.        *)
(*                                                                            *)
(*   Constant - This denotes an instance of a constant.  It has name and      *)
(*  type attributes, where the name must be a declared constant's name and    *)
(*  the type must match the declared constant's generic type.                 *)
(*                                                                            *)
(*   Function Application - This consists of a function subterm and an        *)
(*  argument subterm, where the function's type must be a function type with  *)
(*  domain type equal to the argument's type.                                 *)
(*                                                                            *)
(*   Lambda Abstraction - This consists of a binding variable and a body      *)
(*  subterm.  It bounds the scope of the binding variable to the body, and    *)
(*  this is the only primitive means of bounding variable scope.              *)

type term =
    Tmvar of string * hol_type       (* variable *)
  | Tmconst of string * hol_type     (* constant *)
  | Tmcomb of term * term            (* function application *)
  | Tmabs of term * term;;           (* lambda abstraction *)



(* ** CONSTANT DECLARATION ** *)

(* Constants are introduced to the theory (i.e. "declared") by supplying a    *)
(* name and a generic type.  These are then recorded in a register which can  *)
(* subsequently be queried.  A note that the declaration has taken place is   *)
(* reported, to ensure the user is kept aware of the change to the theory.    *)


(* Constant database *)

(* The constant database registers the name and generic type of all declared  *)
(* constants.  It is implemented as a dynamic lookup tree, indexed by         *)
(* constant name.                                                             *)

let the_consts = ref (dltree_empty : (string,hol_type) dltree);;


(* get_const_gtype : string -> hol_type                                       *)
(*                                                                            *)
(* Returns the generic type of the constant with the supplied name.           *)

let get_const_gtype x =
 try
  dltree_lookup x !the_consts
 with HolFail _ ->
       hol_fail ("get_const_gtype", "No constant called " ^ quote x);;


(* get_all_consts : unit -> (string * hol_type) list                          *)
(*                                                                            *)
(* Returns the name and generic type of each declared constant.               *)

let get_all_consts () =
  let xtys = dltree_elems !the_consts in
  fst_map immutise xtys;;                               (* OCaml protection *)


(* is_const_name : string -> bool                                             *)
(*                                                                            *)
(* The test for whether a given name is the name of a declared constant.      *)

let is_const_name x = (dltree_mem x !the_consts);;


(* Constant declaration command *)

(* prim_new_const : string * hol_type -> unit                                 *)
(*                                                                            *)
(* This is the primitive declaration command for constants.  It takes a       *)
(* string and a type.  The string becomes the name of a new constant in the   *)
(* theory, and the type becomes its generic type.  Any name can be used for a *)
(* constant, but supplying an existing constant's name will cause failure.  A *)
(* note of the declaration is reported, and unit is returned.                 *)

let prim_new_const (x,ty) =
  let func = "prim_new_const" in
  let x_ = immutise x in                                (* OCaml protection *)
  let () = assert1 (not (is_const_name x_))
                 (func, "Constant name " ^ quote x_ ^ " already used") in
  (report ("Declaring constant " ^ quote x_);
   the_consts := dltree_insert (x_,ty) !the_consts);;



(* ** PRIMITIVE UTILITIES ** *)


(* Term comparison *)

let term_eq x y = (Pervasives.compare x y = 0);;

let term_lt x y = (Pervasives.compare x y < 0);;


(* Term type calculation *)

(* A term's type is calculated ultimately from the types of its constituent   *)
(* atoms.  Although potentially a derived utility, it is defined as a         *)
(* primitive for use in 'mk_comb'.                                            *)

let rec type_of tm =
  match tm with
    Tmvar (_,ty) | Tmconst (_,ty)
       -> ty
  | Tmcomb (tm1,_)
       -> snd (dest_fun_type (type_of tm1))
  | Tmabs (v,tm0)
       -> mk_fun_type (type_of v, type_of tm0);;



(* ** PRIMITIVE SYNTAX FUNCTIONS ** *)


(* Variables *)

(* The constructor for variables takes a name and a type, with no             *)
(* restrictions on these arguments.  Note that any name can be used for a     *)
(* variable, including the name of a declared constant.  Any confusion during *)
(* parsing/printing is avoided by using special markers (see 'Lexer' module). *)

let mk_var (x,ty) =
  let x_ = immutise x in                                (* OCaml protection *)
  Tmvar (x_,ty);;

let dest_var tm =
  match tm with
    Tmvar (x_,ty) -> let x = immutise x_ in             (* OCaml protection *)
                     (x,ty)
  | _             -> hol_fail ("dest_var","Not a variable");;

let is_var tm =
  match tm with
    Tmvar _ -> true
  | _       -> false;;


(* Constants *)

(* Two primitive constructors for constants are defined.  Both will only      *)
(* construct a constant that has already been declared and with a type that   *)
(* matches the constant's generic type.                                       *)

(* The first constructor takes just a constant name and returns the constant  *)
(* with its generic type.                                                     *)

let mk_gconst x =
  let (x_,ty0) = try dltree_elem x !the_consts
                 with HolFail _ ->
                   hol_fail ("mk_gconst", "No constant called " ^ quote x) in
  Tmconst (x_,ty0);;

(* The second constructor takes a constant name and an old-to-new tyvar instn *)
(* list, and returns the constant with its generic type's tyvars instantiated *)
(* accordingly.  Note that the instantiation domain is allowed to contain     *)
(* tyvars that are not in the generic type - these are just ignored.          *)

let mk_iconst (x,tytheta) =
  let func = "mk_iconst" in
  let (x_,ty0) = try dltree_elem x !the_consts
                 with HolFail _ ->
                          hol_fail (func, "No constant called " ^ quote x) in
  let ty = try2 (type_inst tytheta) ty0     func in
  Tmconst (x_,ty);;

let dest_const tm =
  match tm with
    Tmconst (x_,ty) -> let x = immutise x_ in           (* OCaml protection *)
                       (x,ty)
  | _               -> hol_fail ("dest_const","Not a constant");;

let is_const tm =
  match tm with
    Tmconst _ -> true
  | _         -> false;;


(* Function application *)

(* The primitive constructor for function application checks that the type of *)
(* the supplied function term is a function type with a domain type equal to  *)
(* the type of the argument term.                                             *)

let mk_comb (tm1,tm2) =
  let func = "mk_comb" in
  let (ty1,ty2) = try1 dest_fun_type (type_of tm1)
                    (func, "Arg 1 type is not a function type") in
  let ty1' = type_of tm2 in
  let () = assert1 (ty1' = ty1)
                    (func, "Function domain type not equal to argument type") in
  Tmcomb (tm1,tm2);;

let dest_comb tm =
  match tm with
    Tmcomb (tm1,tm2) -> (tm1,tm2)
  | _                -> hol_fail ("dest_comb","Not a function application");;

let is_comb tm =
  match tm with
    Tmcomb _ -> true
  | _        -> false;;


(* Lambda abstraction *)

(* The primitive constructor for lambda abstraction checks that the supplied  *)
(* binding variable is indeed a variable.                                     *)

let mk_abs (v,tm0) =
  let () = assert1 (is_var v)       ("mk_abs","Arg 1 is not a variable") in
  Tmabs (v,tm0);;

let dest_abs tm =
  match tm with
    Tmabs (v,tm0) -> (v,tm0)
  | _             -> hol_fail ("dest_abs","Not a lambda abstraction");;

let is_abs tm =
  match tm with
    Tmabs _ -> true
  | _       -> false;;


end;;
