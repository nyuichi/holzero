(* ========================================================================== *)
(* THEORY OF PAIRS (HOL Zero)                                                 *)
(* - Theory defining ordered pairs, plus basic derived properties             *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2009-2010                            *)
(* ========================================================================== *)


module type Pair_sig = sig

  (* Syntax functions *)

  val mk_prod_type : hol_type * hol_type -> hol_type
  val list_mk_prod_type : hol_type list -> hol_type
  val dest_prod_type : hol_type -> hol_type * hol_type
  val strip_prod_type : hol_type -> hol_type list
  val is_prod_type : hol_type -> bool

  val mk_pair : term * term -> term
  val list_mk_pair : term list -> term
  val dest_pair : term -> term * term
  val strip_pair : term -> term list
  val flatstrip_pair : term -> term list
  val is_pair : term -> bool

  (* Definitions *)

  val mk_pair_rep_def : thm
  val is_pair_rep_def : thm
  val prod_def : thm
  val prod_bij_def1 : thm
  val prod_bij_def2 : thm
  val pair_def : thm
  val fst_def : thm
  val snd_def : thm

  (* Theorems *)

  val pair_eq_thm : thm
  val pair_surjective_thm : thm
  val fst_thm : thm
  val snd_thm : thm
  val fst_snd_thm : thm

  (* Inference Rules *)

  val mk_pair_rule : thm -> thm -> thm
  val mk_pair1_rule : thm -> term -> thm
  val mk_pair2_rule : term -> thm -> thm

end;;
