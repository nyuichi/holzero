(* ========================================================================== *)
(* SYSTEM SETTINGS (HOL Zero)                                                 *)
(* - OCaml-specific and installation-specific settings                        *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2016                            *)
(* ========================================================================== *)


(* This file tweaks the OCaml environment and reads in some values from the   *)
(* HOL Zero installation.                                                     *)


(* Check OCaml executable and grab its path *)

(* First we examine the path of the executable that is being run, to check    *)
(* that we're running the right OCaml toplevel, and to work out the           *)
(* directory where it resides.  The OCaml toplevel needs to be 'hzocaml',     *)
(* which incorporates an adjusted lexical syntax and the 'Big_int' module.    *)
(* The directory is used for locating 'hzhelp' if it's not in the execution   *)
(* path.                                                                      *)

let holzero_bindir =
  let exe = Sys.executable_name in
  let i = String.rindex exe '/' + 1 in
  let name = String.sub exe i (String.length exe - i) in
  let () = try assert (name = "hzocaml")
           with Assert_failure _ -> build_error "Not running 'hzocaml'" in
  let dir = String.sub exe 0 (i-1) in
  dir;;


(* HOL Zero version *)

(* This is extracted from the 'VERSION' file in the HOL Zero home directory.  *)
(* Note that the current directory is the HOL Zero 'src' directory.           *)

let holzero_version =
  let ch = try open_in "../VERSION"
           with Sys_error _ ->
             build_error "Missing 'VERSION' file in HOL Zero home directory" in
  let v = input_line ch in    (* read the first line only *)
  let () = close_in ch in
  v;;


(* Interrupt exceptions *)

(* This flag is set to ensure that interactive interrupts raise an Interrupt  *)
(* exception rather than kill the ML session.                                 *)

Sys.catch_break true;;


(* Large stack limit *)

(* Theorem proving can require a large number of non-tail-recursive calls.    *)
(* OCaml's default stack limit is 256 KB.  The stack limit is set here to     *)
(* 50 MB.                                                                     *)

Gc.set { (Gc.get()) with Gc.stack_limit = 50_000_000 };;



(* ** OCAML SPECIAL MEASURES ** *)

(* This section is purely for dealing with OCaml-specific features that would *)
(* otherwise affect system soundness.                                         *)


(* OCaml strings *)

(* OCaml's strings are mutable, i.e. if a new binding is created consisting   *)
(* of a string value from another binding, then updating the string value in  *)
(* either binding will also update it the other.  If used without special     *)
(* measures, this would affect logical soundness, because the names of HOL    *)
(* entities occurring in HOL objects and kernel databases could be updated    *)
(* arbitrarily from outside the logical core.                                 *)

(* The trivial function defined here creates a physical copy of a string, so  *)
(* that updates are independent.  This function is used in the implementation *)
(* of all functions in the interface of the logical core that set or return   *)
(* HOL entity names.  This ensures that HOL entity names in HOL objects and   *)
(* kernel databases can only be updated via the logical core's interface.     *)

let immutise x = String.copy x;;


(* OCaml integers *)

(* OCaml's normal integer datatype, 'int', overflows when values exceed a     *)
(* maximum.  If used without special measures, this would affect logical and  *)
(* parser/printer soundness, because integers are used for the arity of HOL   *)
(* type constants and in the parsing and pretty printing of HOL natural       *)
(* number numerals.                                                           *)

(* These problems are avoided by using OCaml's 'big_int' datatype inside the  *)
(* logical core and in the parser and pretty printer.  This datatype has no   *)
(* limits on the size of integers that can be represented.  Note that the     *)
(* 'Big_int' module needs to have been already loaded into the OCaml          *)
(* toplevel, and that this is done in the creation of the 'hzocaml' toplevel. *)

open Big_int;;

let big_int_0 = big_int_of_int 0;;
let big_int_1 = big_int_of_int 1;;
let big_int_2 = big_int_of_int 2;;

let print_big_int n =
  (Format.open_hbox ();
   Format.print_string (string_of_big_int n);
   Format.close_box ());;


(* Type-unsafe functions in OCaml libraries *)

(* The OCaml library features some type-unsafe functions with could           *)
(* potentially be used to circumvent the HOL Zero langauge and inference      *)
(* kernels to result in logical unsoundness.  The following functions are     *)
(* type-unsafe:                                                               *)
(*  'obj' and 'magic' (from 'Obj' module)                                     *)
(*     - these can turn program values into arbitrary datatypes;              *)
(*  'from_channel' and 'from_string' (from 'Marshal' module)                  *)
(*     - these can read data into arbitrary datatypes                         *)
(*  'input_value' (from 'Pervasives' module)                                  *)
(*     - this can read data into arbitrary datatypes                          *)

(* This problem is circumvented by overwriting these unsafe functions with    *)
(* versions that always raise HolError exceptions.                            *)

let unsafe_error f =
  hol_error (f, "This type-unsafe function is overwritten in HOL Zero");;

module Obj =
  struct
     include Obj;;
     let obj (x:Obj.t) = unsafe_error "Obj.obj";;
     let magic x = unsafe_error "Obj.magic";;
  end;;

module Marshal =
  struct
     include Marshal;;
     let from_channel (x:in_channel) = unsafe_error "Marshal.from_channel";;
     let from_string (x:string) (y:int) = unsafe_error "Marshal.from_string";;
  end;;

module Pervasives =
  struct
     include Pervasives;;
     let input_value (x:in_channel) = unsafe_error "Pervasives.input_value";;
  end;;

let input_value = Pervasives.input_value;;
