(* ========================================================================== *)
(* EXCEPTIONS (HOL Zero)                                                      *)
(* - Definitions of HOL Zero's general purpose exceptions                     *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2013                            *)
(* ========================================================================== *)


module type Exn_sig = sig

  (* Exceptions *)

  exception HolFail of string * string
  val hol_fail : string * string -> 'a

  exception HolError of string * string
  val hol_error : string * string -> 'a
  val internal_error : string -> 'a
  val build_error : string -> 'a

  exception LocalFail

  val print_exn : exn -> unit

end;;
