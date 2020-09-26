(* ========================================================================== *)
(* DISPLAY MODES (HOL Zero)                                                   *)
(* - Display modes for configuring pretty printer output                      *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2013                            *)
(* ========================================================================== *)


module DModes : DModes_sig = struct


(* This module implements the display modes mechanism, for configuring how    *)
(* the pretty printers display types and terms.  Note that the display modes  *)
(* make no difference to the way that types and terms are parsed.             *)


(* 'level' datatype *)

type level = Minimal | Full;;

let string_of_level l =
  match l with
    Minimal -> "Minimal"
  | Full    -> "Full";;


(* Type annotation mode *)

(* This is used to determine which term atoms are type-annotated in printed   *)
(* output.  In 'Minimal' mode, which is sufficient for disambiguation, a      *)
(* minimal set of atoms to be annotated is chosen according to a heuristic    *)
(* with the intention of maximising readability.  In 'Full' mode, every var   *)
(* atom and every polymorphic const atom is type-annotated.  The default      *)
(* setting is 'Minimal'.                                                      *)

let the_type_annotation_mode = ref Minimal;;

let set_type_annotation_mode l =
  (report ("Setting type annotation mode to " ^ string_of_level l);
   the_type_annotation_mode := l);;

let get_type_annotation_mode () = !the_type_annotation_mode;;


(* Type variable marking mode *)

(* This is used to determine which tyvars are marked with an apostrophe char  *)
(* prepended to their name in printed output.  In 'Minimal' mode, which is    *)
(* sufficient for disambiguation, only those tyvars with a name that clashes  *)
(* with a type constant's name are marked.  In 'Full' mode, all tyvars are    *)
(* marked.  The default setting is 'Full'.                                    *)

let the_tyvar_marking_mode = ref Full;;

let set_tyvar_marking_mode l =
  (report ("Setting type variable annotation mode to " ^ string_of_level l);
   the_tyvar_marking_mode := l);;

let get_tyvar_marking_mode () = !the_tyvar_marking_mode;;


(* Variable marking mode *)

(* This is used to determine which vars are marked with a '%' char prepended  *)
(* to their name in printed output.  In 'Minimal' mode, which is sufficient   *)
(* for disambiguation, only those vars with a name that clashes with a        *)
(* constant's name are marked.  In 'Full' mode, all variables are marked.     *)
(* The default setting is 'Minimal'.                                          *)

let the_var_marking_mode = ref Minimal;;

let set_var_marking_mode l =
  (report ("Setting variable annotation mode to " ^ string_of_level l);
   the_var_marking_mode := l);;

let get_var_marking_mode () = !the_var_marking_mode;;


(* Language level mode *)

(* This is used to determine whether primitive or full HOL language term      *)
(* syntax is printed.  The 'Minimal' mode is for primitive syntax.  The       *)
(* default setting is 'Full'.                                                 *)

let the_language_level_mode = ref Full;;

let set_language_level_mode l =
  (report ("Setting language level mode to " ^ string_of_level l);
   the_language_level_mode := l);;

let get_language_level_mode () = !the_language_level_mode;;


(* Display modes summary *)

let show_display_modes () =
  (print_string "HOL Zero Display Modes\n";
   print_string ("   Type annotation mode:        " ^
                       string_of_level (get_type_annotation_mode ()) ^ "\n");
   print_string ("   Variable marking mode:       " ^
                       string_of_level (get_var_marking_mode ()) ^ "\n");
   print_string ("   Type variable marking mode:  " ^
                       string_of_level (get_tyvar_marking_mode ()) ^ "\n");
   print_string ("   Language level mode:         " ^
                       string_of_level (get_tyvar_marking_mode ()) ^ "\n"));;


end;;
