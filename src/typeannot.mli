(* ========================================================================== *)
(* TYPE ANNOTATION (HOL Zero)                                                 *)
(* - Type annotation of preterms                                              *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2011                            *)
(* ========================================================================== *)


module type TypeAnnot_sig = sig

  open Preterm

  (* Type annotation *)

  val full_annotate_preterm  : bool -> preterm -> preterm
  val min_annotate_preterm  : pretype option -> preterm -> preterm

end;;
