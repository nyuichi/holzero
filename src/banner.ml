(* ========================================================================== *)
(* BANNER (HOL Zero)                                                          *)
(* - A banner printer for HOL Zero                                            *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2010-2016                            *)
(* ========================================================================== *)


module Banner : Banner_sig = struct


(* The banner gets printed at the end of loading the base system, indicating  *)
(* to the user that the system has successfully loaded.                       *)


(* print_banner : unit -> unit                                                *)

let print_banner () =
  let n = String.length holzero_version in
  let left_space = String.make (44 - n) ' ' in
  (print_string "\n\n";
   print_string "         0   0  000  0       00000 00000 0000   000\n";
   print_string "         0   0 0   0 0          0  0     0   0 0   0\n";
   print_string "         00000 0   0 0         0   000   0000  0   0\n";
   print_string "         0   0 0   0 0        0    0     0 0   0   0\n";
   print_string "         0   0  000  00000   00000 00000 0  0   000\n";
   print_string "\n";
   print_string (left_space ^ "Version " ^ holzero_version ^ "\n");
   print_string "\n";
   print_string "       Copyright (c) Proof Technologies Ltd, 2008-2016\n";
   print_string "\n");;


end;;
