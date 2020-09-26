(* ========================================================================== *)
(* TYPE ANALYSIS (HOL Zero)                                                   *)
(* - Type analysis of pretypes and preterms                                   *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2012                            *)
(* ========================================================================== *)


module type TypeAnal_sig = sig

  open Type
  open Term
  open Preterm

  (* Detyping *)

  val new_pretype_gvar : unit -> pretype
  val detype_preterm : preterm -> preterm

  (* Checks *)

  val check_pretype : pretype -> pretype
  val check_preterm_annotations : term -> preterm -> preterm

  (* Type unification *)

  val theta_closure : (pretype * pretype) list -> (pretype * pretype) list ->
                                                       (pretype * pretype) list
  val unify_pretypes0 : (pretype * pretype) list -> pretype * pretype ->
                                                       (pretype * pretype) list
  val unify_pretypes : pretype * pretype -> (pretype * pretype) list
  val unify_pretype_list : (pretype * pretype) list -> pretype list ->
                                                       (pretype * pretype) list
  val unify_pretype_pairs :
                 (pretype * pretype) list -> (pretype * pretype) list ->
                                                       (pretype * pretype) list

  (* Type inference *)

  val infer_pretypes : preterm -> (pretype * pretype) list
  val resolve_preterm : preterm -> preterm

end;;
