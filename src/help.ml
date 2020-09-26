(* ========================================================================== *)
(* HELP FACILITY (HOL Zero)                                                   *)
(* - A help facility for HOL Zero commands and terminology                    *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2010-2013                            *)
(* ========================================================================== *)


module Help : Help_sig = struct


(* A help facility is defined here, based on the the User Manual appendices.  *)
(* Its functionality is implemented by the "hzhelp" bash script, which can    *)
(* also be called directly from the Unix command line.                        *)


(* help : string -> unit                                                      *)
(*                                                                            *)
(* This is a help facility for HOL Zero commands and HOL terminology.  If the *)
(* supplied string is a HOL Zero ML command, then the user manual A-appendix  *)
(* entry for this command is displayed.  If the supplied string is a space-   *)
(* separated series of A-appendix numbers (e.g. "A3 A4 A5"), then the         *)
(* signature of each entry is listed for those appendices given by the        *)
(* numbers.  If the supplied string is "all-commands", then the signatures of *)
(* all A-appendix entries are listed.                                         *)
(*                                                                            *)
(* If the supplied string is a HOL Zero theorem name, then the user manual    *)
(* B1- or B2-appendix entry for this theorem is displayed.  If the supplied   *)
(* string is "all-theorems", the names of all B1- and B2-appendix theorems    *)
(* are listed.                                                                *)
(*                                                                            *)
(* If the supplied string is a word defined in the glossary, then the entry   *)
(* for that word is displayed.  If the supplied string is "all-words", then   *)
(* the names of all words defined in the glossary are listed.                 *)

let help obj =
  let help_cmd = quote (holzero_bindir ^ "/hzhelp") in
  let err = Sys.command (help_cmd ^ " " ^ quote obj ^ " 2> /dev/null") in
  match err with
    0 -> ()
  | 1 -> hol_fail ("help", "Missing argument")
  | 2 -> hol_fail ("help", "Missing HOL Zero home directory")
  | 3 -> hol_fail ("help", "Missing HOL Zero 'doc' directory")
  | 4 -> hol_fail ("help", "Missing HOL Zero 'doc/User_Manual' directory")
  | 5 -> hol_fail ("help", "Missing 'Glossary.txt' in 'doc' directory")
  | 6 -> hol_fail ("help", "Missing supplied A-appendix file number")
  | 7 -> hol_fail ("help", "More than one A-appendix entry found for command")
  | 8 -> hol_fail ("help", "Cannot find appendix or glossary entry \
                            for supplied argument")
  | _ -> internal_error "help";;


end;;
