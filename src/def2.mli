(* ========================================================================== *)
(* DEFINITION II (HOL Zero)                                                   *)
(* - Derived definition commands for non-recursive and recursive functions    *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2010                            *)
(* ========================================================================== *)


module type Def2_sig = sig

  (* Non-recursive function definition *)

  val new_fun_definition : term -> thm
  val get_fun_definition : string -> thm
  val get_all_fun_definitions : unit -> (string * thm) list

  (* Recursive function definition *)

  val new_recursive_fun_definition : thm -> term -> thm

end;;
