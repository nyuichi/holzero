(* ========================================================================== *)
(* DISPLAY MODES (HOL Zero)                                                   *)
(* - Display modes for configuring pretty printer output                      *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2012                            *)
(* ========================================================================== *)


module type DModes_sig = sig

  (* Display modes *)

  type level = Minimal | Full

  val set_type_annotation_mode : level -> unit
  val get_type_annotation_mode : unit -> level

  val set_tyvar_marking_mode : level -> unit
  val get_tyvar_marking_mode : unit -> level

  val set_var_marking_mode : level -> unit
  val get_var_marking_mode : unit -> level

  val set_language_level_mode : level -> unit
  val get_language_level_mode : unit -> level

  val show_display_modes : unit -> unit

end;;
