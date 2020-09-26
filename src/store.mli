(* ========================================================================== *)
(* THEOREM STORAGE (HOL Zero)                                                 *)
(* - Databases for theorems and lemmas                                        *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2011                            *)
(* ========================================================================== *)


module type Store_sig = sig

  open Thm

  (* Theorem storage *)

  val save_thm : string * thm -> thm
  val get_thm : string -> thm
  val get_all_thms : unit -> (string * thm) list

  (* Lemma storage *)

  val save_lemma : string * thm -> thm
  val get_lemma : string -> thm
  val get_all_lemmas : unit -> (string * thm) list

end;;
