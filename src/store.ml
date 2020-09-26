(* ========================================================================== *)
(* THEOREM STORAGE (HOL Zero)                                                 *)
(* - Databases for theorems and lemmas                                        *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2012                            *)
(* ========================================================================== *)


module Store : Store_sig = struct


(* This module implements databases for storing theorems and lemmas under a   *)
(* name index.  Like axioms, stored theorems are restricted to having no      *)
(* free variables or assumptions, whereas stored lemmas are theorems that     *)
(* no such restrictions.                                                      *)


open DLTree;;

open Thm;;
open Utils1;;
open Utils2;;



(* ** THEOREM STORAGE ** *)

(* The first database is for stored theorems.  This is intended for theorem   *)
(* results for general usage, and so its theorems are restricted to having no *)
(* free variables and no assumptions.                                         *)


(* The theorem database *)

let the_theorems = ref (dltree_empty : (string,thm) dltree);;

let get_thm x =
 try
  dltree_lookup x !the_theorems
 with HolFail _ -> hol_fail ("get_thm", "No theorem called " ^ quote x);;

let get_all_thms () =
  let xths = dltree_elems !the_theorems in
  fst_map immutise xths;;                               (* OCaml protection *)


(* Theorem storage command *)

(* save_thm : string * thm -> thm                                             *)
(*                                                                            *)
(* This is the theorem storage command.  It takes a string and a theorem      *)
(* argument.  The theorem gets stored in the database under the string index. *)
(* The string must not be used for the name of an existing theorem (unless in *)
(* benign redefinition), and the theorem must not contain free variables or   *)
(* or assumptions.                                                            *)

let save_thm (x,th) =
  let func = "save_thm" in
  let x_ = immutise x in                                (* OCaml protection *)
 try
  let () = assert1 (is_empty (asms th))     (func,"Assumptions not allowed") in
  let () = assert1 (is_empty (thm_free_vars th))
                                            (func,"Free vars not allowed") in
  let () = assert0 (cannot get_thm x_)     LocalFail in
  (report ("Storing theorem " ^ quote x_);
   the_theorems := dltree_insert (x_,th) !the_theorems;
   th)
 with LocalFail ->
  (* Benign redefinition *)
  let th0 = get_thm x in
  let () = assert1 (thm_alpha_eq th th0)
                       (func, "Theorem name " ^ quote x ^ " already used") in
  (warn ("Benign redefinition of theorem " ^ quote x);
   th);;



(* ** LEMMA STORAGE ** *)

(* The second database is for stored lemmas.  This is intended for storing    *)
(* intermediate theorem results that are not necessarily in an ideal form for *)
(* for general usage, and there are no restrictions on its theorems.          *)


(* The lemma database *)

let the_lemmas = ref (dltree_empty : (string,thm) dltree);;

let get_lemma x =
 try
  dltree_lookup x !the_lemmas
 with HolFail _ -> hol_fail ("get_lemma", "No lemma called " ^ quote x);;

let get_all_lemmas () =
  let xths = dltree_elems !the_lemmas in
  fst_map immutise xths;;                               (* OCaml protection *)


(* Lemma storage command *)

(* save_lemma : string * thm -> thm                                           *)
(*                                                                            *)
(* This is the lemma storage command.  It takes a string and a theorem        *)
(* argument.  The theorem gets stored in the database under the string index. *)
(* The string must not be used for the name of an existing lemma (unless in   *)
(* benign redefinition).                                                      *)

let save_lemma (x,th) =
  let func = "save_lemma" in
  let x_ = immutise x in                                (* OCaml protection *)
 try
  let () = assert0 (cannot get_lemma x_)      LocalFail in
  (report ("Storing lemma " ^ quote x_);
   the_lemmas := dltree_insert (x_,th) !the_lemmas;
   th)
 with LocalFail ->
  (* Benign redefinition *)
  let th0 = get_lemma x in
  let () = assert1 (thm_alpha_eq th th0)
                         (func, "Lemma name " ^ quote x ^ " already used") in
  (warn ("Benign redefinition of lemma " ^ quote x);
   th);;


end;;
