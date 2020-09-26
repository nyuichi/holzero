(* ========================================================================== *)
(* NATURAL NUMBER ARITHMETIC (HOL Zero)                                       *)
(* - Theory defining natural number operators/numerals; derived properties    *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2009-2011                            *)
(* ========================================================================== *)


module type NatArith_sig = sig

  (* Definitions *)

  val pre_def : thm
  val add_def : thm
  val sub_def : thm
  val mult_def : thm
  val exp_def : thm
  val even_def : thm
  val odd_def : thm

  (* Syntax functions *)

  val mk_pre : term -> term
  val dest_pre : term -> term
  val is_pre : term -> bool

  val mk_add : term * term -> term
  val dest_add : term -> term * term
  val is_add : term -> bool

  val mk_sub : term * term -> term
  val dest_sub : term -> term * term
  val is_sub : term -> bool

  val mk_mult : term * term -> term
  val dest_mult : term -> term * term
  val is_mult : term -> bool

  val mk_exp : term * term -> term
  val dest_exp : term -> term * term
  val is_exp : term -> bool

  val mk_even : term -> term
  val dest_even : term -> term
  val is_even : term -> bool

  val mk_odd : term -> term
  val dest_odd : term -> term
  val is_odd : term -> bool

  (* Theorems *)

  val pre_suc_thm : thm
  val pre_zero_thm : thm

  val add_id_thm : thm
  val add_comm_thm : thm
  val add_assoc_thm : thm
  val suc_add_thm : thm
  val add_dist_right_suc_thm : thm
  val add_dist_left_suc_thm : thm

  val sub_right_id_thm : thm
  val sub_dist_right_suc_thm : thm
  val suc_sub_suc_thm : thm
  val sub_cancel_thm : thm
  val add_sub_cancel_thm : thm

  val mult_zero_thm : thm
  val mult_id_thm : thm
  val mult_comm_thm : thm
  val mult_assoc_thm : thm
  val mult_dist_left_suc_thm : thm
  val mult_dist_right_suc_thm : thm
  val mult_dist_left_add_thm : thm
  val mult_dist_right_add_thm : thm
  val twice_thm : thm

  val exp_right_zero_thm : thm
  val exp_right_id_thm : thm
  val exp_dist_right_suc_thm : thm
  val exp_dist_right_add_thm : thm

  val zero_even_thm : thm
  val zero_not_odd_thm : thm
  val one_odd_thm : thm
  val even_suc_thm : thm
  val odd_suc_thm : thm
  val twice_even_thm : thm
  val suc_twice_odd_thm : thm

end;;
