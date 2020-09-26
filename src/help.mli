(* ========================================================================== *)
(* HELP FACILITY (HOL Zero)                                                   *)
(* - A help facility for HOL Zero commands and terminology                    *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2010-2013                            *)
(* ========================================================================== *)


module type Help_sig = sig

  val help : string -> unit

end;;
