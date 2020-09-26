(* ========================================================================== *)
(* EXCEPTIONS (HOL Zero)                                                      *)
(* - Definitions of HOL Zero's general purpose exceptions                     *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2013                            *)
(* ========================================================================== *)


module Exn : Exn_sig = struct


(* This module defines three new exceptions for general usage, together with  *)
(* a printer for exceptions for overriding OCaml's existing one.              *)


(* HolFail exception *)

(* This exception is for errors that can ultimately reach the top level, but  *)
(* that may also get trapped by calling functions.  It is the classic         *)
(* exception for error cases in HOL Zero functions.  It consists of the name  *)
(* of the function that fails and a message describing the error in some      *)
(* detail.  Various supporting functions for raising and trapping HolFails    *)
(* are defined below.                                                         *)

exception HolFail of string * string;;

let hol_fail (func,msg) = raise (HolFail (func,msg));;


(* HolError exception *)

(* This exception is for short-circuit errors that directly drop out at the   *)
(* top level, avoiding any traps for HolFail exceptions.  It consists of a    *)
(* string that broadly classifies the error (by convention written in         *)
(* uppercase) and a message describing the error in some detail.              *)

exception HolError of string * string;;

let hol_error (err,msg) = raise (HolError (err,msg));;

let internal_error func = hol_error ("INTERNAL ERROR", func);;

let build_error msg = hol_error ("BUILD ERROR", msg);;


(* LocalFail exception *)

(* This exception is for simple local control flow, raised to escape from the *)
(* main part of a function and typically caught in an outer exception trap of *)
(* the same function.  This can be useful for removing error-reporting        *)
(* clutter from the main body of a function and grouping it together at the   *)
(* end.  It is also used as a last resort in non-error control flow, when     *)
(* there is nothing more elegant in ML.                                       *)

exception LocalFail;;


(* print_exn : exn -> unit                                                    *)
(*                                                                            *)
(* This is a printer for exceptions that prints HolFails and HolErrs nicely,  *)
(* and everything else the same as normal.                                    *)

let print_exn e =
  match e with
    HolFail (func,msg)
       -> Format.print_string ("\n[HZ] FAIL: " ^ func ^ " - " ^ msg)
  | HolError (err,msg)
       -> Format.print_string ("\n[HZ] " ^ err ^ ": " ^ msg)
  | _  -> Format.print_string (Printexc.to_string e);;


end;;
