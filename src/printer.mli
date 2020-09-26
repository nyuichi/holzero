(* ========================================================================== *)
(* PRINTER (HOL Zero)                                                         *)
(* - Pretty printers for types, terms and theorems                            *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2015                            *)
(* ========================================================================== *)


module type Printer_sig = sig

  open Type
  open Term
  open Thm
  open DModes

  (* Pretty printers *)

  val print_type : hol_type -> unit
  val print_qtype : hol_type -> unit

  val print_term : term -> unit
  val print_qterm : term -> unit

  val print_thm : thm -> unit

end;;
