(* ========================================================================== *)
(* DEFINITION I (HOL Zero)                                                    *)
(* - Derived definition commands for constants                                *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2011                            *)
(* ========================================================================== *)


module type Def1_sig = sig

  (* Type bijections definition *)

  val new_type_bijections : string -> string * string -> thm * thm
  val get_type_bijections : string -> thm * thm
  val get_type_bijection_info : string -> (string * string) * (thm * thm)
  val get_all_type_bijections : unit -> (string * (thm * thm)) list
  val get_all_type_bijection_info :
                      unit -> (string * ((string * string) * (thm * thm))) list

end;;
