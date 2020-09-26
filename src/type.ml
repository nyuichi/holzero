(* ========================================================================== *)
(* TYPES (HOL Zero)                                                           *)
(* - Datatype for internal types plus support for type constant declaration   *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2016                            *)
(* ========================================================================== *)


module Type : Type_sig = struct


(* This module defines the internal representation of HOL types.  This is     *)
(* done by defining an abstract datatype for types, and then primitive syntax *)
(* functions for constructing and destructing types, and support for type     *)
(* constant declaration.  The primitive syntax constructors ensure that only  *)
(* well-formed types can be constructed.  This module is a trusted component  *)
(* of the system.                                                             *)

(* Also defined in this module are some primitive utilities (for function     *)
(* type syntax and for type instantiation) needed to define HOL terms.        *)

(* The 'immutise' function is used wherever string inputs/outputs set/return  *)
(* internal string values, to avoid OCaml string mutability problems (see     *)
(* 'system.ml').                                                              *)


open DLTree;;



(* ** TYPE DATATYPE ** *)


(* hol_type *)

(* This is the datatype for internal HOL types.  It has 2 classes,            *)
(* corresponding to the 2 primitive syntactic categories of types:            *)
(*                                                                            *)
(*   Type Variable - This denotes an occurrence of a type variable.  It has   *)
(*  just a name attribute.  Any two occurrences of type variables within a    *)
(*  given object represent the same entity iff they have the same name.       *)
(*                                                                            *)
(*   Compound Type - This denotes an instance of a type constant.  It has     *)
(*  name and type parameter list attributes, where the name must be the name  *)
(*  of a declared type constant, and the parameter list length must equal the *)
(*  declared type constant's arity.                                           *)

type hol_type =
    Tyvar of string                       (* type variable *)
  | Tycomp of string * hol_type list;;    (* compound type *)



(* ** TYPE CONSTANT DECLARATION ** *)

(* Type constants are introduced to the theory (i.e. "declared") by supplying *)
(* a name and an arity.  These are then recorded in a register which can      *)
(* subsequently be queried.  A note that the declaration has taken place is   *)
(* reported, to ensure the user is kept aware of the change to the theory.    *)


(* Type constant database *)

(* The type constant database registers the name and arity of all declared    *)
(* type constants.  It is implemented as a dynamic lookup tree, indexed by    *)
(* type constant name.  Arities are stored as OCaml 'big_int' integers.       *)

let the_tyconsts = ref (dltree_empty : (string,big_int) dltree);;


(* prim_get_tyconst_arity : string -> big_int                                 *)
(*                                                                            *)
(* Returns the arity of the type constant with the supplied name.  The arity  *)
(* is given as an OCaml 'big_int' integer.                                    *)

let prim_get_tyconst_arity x =
 try
  dltree_lookup x !the_tyconsts
 with HolFail _ ->
        hol_fail ("get_tyconst_arity", "No type constant called " ^ quote x);;


(* prim_get_all_tyconsts : unit -> (string * big_int) list                    *)
(*                                                                            *)
(* Returns the name and arity of each declared type constant.  Arities are    *)
(* given as OCaml 'big_int' integers.                                         *)

let prim_get_all_tyconsts () =
  let xns = dltree_elems !the_tyconsts in
  fst_map immutise xns;;                                (* OCaml protection *)


(* is_tyconst_name : string -> bool                                           *)
(*                                                                            *)
(* The test for whether a given name is the name of a declared type constant. *)

let is_tyconst_name x = (dltree_mem x !the_tyconsts);;


(* Type constant declaration command *)

(* This is the primitive declaration command for type constants.  It takes    *)
(* name 'x' and arity 'n' (as an OCaml big_int), and declares a new type      *)
(* constant with these attributes.  Any name can be used, except that it      *)
(* cannot be the same as an existing type constant's name.  A note of the     *)
(* declaration is reported, and unit is returned.                             *)

let prim_new_tyconst (x,n) : unit =
  let func = "prim_new_tyconst" in
  let x_ = immutise x in                                (* OCaml protection *)
  let () = assert1 (ge_big_int n big_int_0)
                                       (func, "Arity must be non-negative") in
  let () = assert1 (not (is_tyconst_name x_))
                 (func, "Type constant name " ^ quote x_ ^ " already used") in
  (report ("Declaring type constant " ^ quote x_);
   the_tyconsts := dltree_insert (x_,n) !the_tyconsts);;



(* ** PRIMITIVE SYNTAX FUNCTIONS ** *)


(* Type variables *)

(* Any name can be used for a type variable, including the name of a declared *)
(* type constant.  Any confusion during parsing/printing is avoided by using  *)
(* special markers (see 'Lexer' module).                                      *)

let mk_var_type x =
  let x_ = immutise x in                                (* OCaml protection *)
  Tyvar x_;;

let dest_var_type ty =
  match ty with
    Tyvar x_ -> let x = immutise x_ in                  (* OCaml protection *)
                x
  | _        -> hol_fail ("dest_var_type","Not a type variable");;

let is_var_type ty =
  match ty with
    Tyvar _ -> true
  | _       -> false;;


(* Compound types *)

(* The primitive constructor for compound types checks that the type constant *)
(* has been declared and that the argument list length equals the type        *)
(* constant's arity.                                                          *)

let mk_comp_type (x,tys) =
  let func = "mk_comp_type" in
  let (x_,n) = try dltree_elem x !the_tyconsts
               with HolFail _ ->
                    hol_fail (func, "No type constant called " ^ quote x) in
  let () = assert1 (eq_big_int n (length_big_int tys))
                                    (func, "Type list doesn't fit arity") in
  Tycomp (x_,tys);;

let dest_comp_type ty =
  match ty with
    Tycomp (x_,tys) -> let x = immutise x_ in           (* OCaml protection *)
                       (x,tys)
  | _               -> hol_fail ("dest_comp_type","Not a compound type");;

let is_comp_type ty =
  match ty with
    Tycomp _ -> true
  | _        -> false;;



(* ** PRIMITVE UTILITIES ** *)

(* These functions are derivable from the primitive syntax functions, but are *)
(* implemented here as primitives for use in the 'Term' module.               *)


(* Type comparison *)

let type_eq x y = (Pervasives.compare x y = 0);;

let type_lt x y = (Pervasives.compare x y < 0);;


(* Function types *)

(* Syntax functions are provided for the function type operator, since these  *)
(* are used in the primitive syntax functions for terms.  Note that these ML  *)
(* functions are implemented in anticipation of the introduction of the HOL   *)
(* function type operator in the 'CoreThry' module.                           *)

(* A function type has domain and range type parameters.                      *)

let mk_fun_type (ty1,ty2) = Tycomp ("->",[ty1;ty2]);;

let dest_fun_type ty =
  match ty with
    Tycomp ("->",[ty1;ty2])
       -> (ty1,ty2)
  | _  -> hol_fail ("dest_fun_type","Not a function type");;

let is_fun_type ty =
  match ty with
    Tycomp ("->",[ty1;ty2])
       -> true
  | _  -> false;;


(* Type instantiation *)

(* This takes an old-to-new tyvar instn list and a type, and replaces tyvars  *)
(* in the type according to the instn list, keeping all other tyvars the      *)
(* same.  Instn list entries that do not apply to the type are ignored, as    *)
(* are repeated entries for a given tyvar (beyond its first entry).  Non-     *)
(* tyvars in the instn domain cause failure.                                  *)

(* Special care is taken not to reconstruct subtypes that have not changed as *)
(* a result of the instantiation, to save on unnecessary garbage collection.  *)

let rec type_inst0 tytheta ty =
  match ty with
    Tyvar _
       -> (try  assoc ty tytheta  with HolFail _ ->  ty)
  | Tycomp (x,tys)
       -> let tys' = map (type_inst0 tytheta) tys in
          if (list_eq (==) tys' tys)  then ty  else mk_comp_type (x,tys');;

let type_inst tytheta ty =
  match tytheta with
    [] -> ty
  | _  -> let () = assert1 (forall (is_var_type <* fst) tytheta)
                   ("type_inst","Non-type-variable in instantiation domain") in
          type_inst0 tytheta ty;;


end;;
