(* ========================================================================== *)
(*                         HOL ZERO BASE SYSTEM                               *)
(*                                                                            *)
(* A basic theorem prover for the HOL logic.                                  *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2016                            *)
(* ========================================================================== *)


(* This is the top-level build file for the HOL Zero base system.             *)



(* ** INITIAL SETTINGS ** *)

(* First some library modules and system settings, to set the context in      *)
(* which HOL Zero is defined.  Included is 'use_file', for use in preference  *)
(* to OCaml's '#use' directive, which does not exit from nested failure.      *)


(* Basic setup *)

#use "exn.mli";;
#use "exn.ml";;
open Exn;;
#install_printer Exn.print_exn;;

#directory "+compiler-libs";;
let use_file file =
  let success = Toploop.use_file Format.std_formatter file in
  if not success
    then (if not (Sys.file_exists file)
           then build_error ("Cannot find file '" ^ file ^ "'")
           else build_error ("Build failed whilst processing '" ^ file ^ "'"));;

use_file "system.ml";;
#install_printer print_big_int;;


(* Libraries *)

use_file "lib.mli";;
use_file "lib.ml";;
open Lib;;

use_file "dltree.mli";;
use_file "dltree.ml";;

use_file "reader.mli";;
use_file "reader.ml";;



(* ** CORE SYSTEM ** *)

(* The core system defines HOL Zero's logical core by setting up the language *)
(* kernel, the inference kernel and the core theory.  It also provides some   *)
(* basic facilities, including a parser and pretty printer for HOL type and   *)
(* term quotations.                                                           *)


(* Language kernel *)

(* Firstly a kernel for the internal representation of HOL language.          *)

use_file "type.mli";;
use_file "type.ml";;

use_file "term.mli";;
use_file "term.ml";;


(* Inference kernel *)

(* Next the inference kernel, to provide the logical core with the basic      *)
(* mechanisms for logical deduction and theory assertion.                     *)

use_file "utils1.mli";;
use_file "utils1.ml";;

use_file "thm.mli";;
use_file "thm.ml";;


(* Quotation parsers and pretty printers *)

(* The parsers and pretty printers enable HOL quotations to be read in and    *)
(* displayed respectively.  Support for setting display modes and the         *)
(* syntactic status of identifiers is included.                               *)

use_file "names.mli";;
use_file "names.ml";;

use_file "dmodes.mli";;
use_file "dmodes.ml";;

use_file "lexer.mli";;
use_file "lexer.ml";;

use_file "preterm.mli";;
use_file "preterm.ml";;

use_file "typeanal.mli";;
use_file "typeanal.ml";;

use_file "typeannot.mli";;
use_file "typeannot.ml";;

use_file "parser.mli";;
use_file "parser.ml";;
Quotation.add "hol" (Quotation.ExStr (fun _ -> Parser.expand_hol_quotation));;

use_file "printer.mli";;
use_file "printer.ml";;
#install_printer Printer.print_qtype;;
#install_printer Printer.print_qterm;;
#install_printer Printer.print_thm;;


(* Core theory *)

(* The core theory introduces the theory entities alluded to in the inference *)
(* kernel.  This completes the logical core.                                  *)

use_file "corethry.mli";;
use_file "corethry.ml";;


(* Utilities *)

(* Some basic derived facilities are added, to complete the core system.      *)

use_file "utils2.mli";;
use_file "utils2.ml";;

use_file "wrap.mli";;
use_file "wrap.ml";;

use_file "store.mli";;
use_file "store.ml";;


(* Module inclusion for core system *)

include Type;;
include Term;;
include Thm;;
include CoreThry;;

include Utils1;;
include Utils2;;
include Names;;
include DModes;;
include Parser;;
include Printer;;
include Wrap;;
include Store;;



(* ** BASIC EXTENSIONS ** *)

(* Some basic extensions are now built on top of the core system.  These      *)
(* consist of derived support for lambda calculus and predicate logic,        *)
(* various forms of derived definition command, and new theory for pairs and  *)
(* natural numbers.                                                           *)


(* Equality and booleans *)

(* The support for lambda calculus and predicate logic is boosted here by     *)
(* extending the theory with some extra constants and adding various derived  *)
(* theorems and inference rules.  Predicate logic derivations relying on the  *)
(* Axiom of Choice are separated out into their own module ('BoolClass').     *)

use_file "equal.mli";;
use_file "equal.ml";;

use_file "bool.mli";;
use_file "bool.ml";;

use_file "eqcong.mli";;
use_file "eqcong.ml";;

use_file "boolalg.mli";;
use_file "boolalg.ml";;

use_file "boolclass.mli";;
use_file "boolclass.ml";;


(* Pairs and extra definition facilities *)

(* Derived definition facilities are added here, for more advanced forms of   *)
(* definition.  These are then used to extend the theory with pairs, which    *)
(* are in turn used in further derived definition facilities.                 *)

use_file "def1.mli";;
use_file "def1.ml";;

use_file "pair.mli";;
use_file "pair.ml";;

use_file "def2.mli";;
use_file "def2.ml";;


(* Infinity and natural numbers *)

(* The theory is extended with an infinite cardinality type here, and this is *)
(* then used to define the natural numbers and their arithmetic operators.    *)
(* Natural number numerals are also defined, together with conversions for    *)
(* evaluating arithmetic on them.                                             *)

use_file "ind.mli";;
use_file "ind.ml";;

use_file "nat.mli";;
use_file "nat.ml";;

use_file "natnumrl.mli";;
use_file "natnumrl.ml";;

use_file "natarith.mli";;
use_file "natarith.ml";;

use_file "natrel.mli";;
use_file "natrel.ml";;

use_file "nateval.mli";;
use_file "nateval.ml";;


(* Module inclusion for basic extensions *)

open Def1;;
open Def2;;

open Equal;;
open EqCong;;
open Bool;;
open BoolAlg;;
open BoolClass;;
open Pair;;
open Ind;;
open Nat;;
open NatNumrl;;
open NatArith;;
open NatRel;;
open NatEval;;


(* Common HOL *)

(* The Common HOL API is provided, giving portability across HOL systems.     *)

use_file "commonhol.mli";;
use_file "commonhol.ml";;


(* Miscellaneous *)

(* Finally a help facility and a HOL Zero banner printer are added.  The      *)
(* banner gets printed iff the build has completed successfully.              *)

use_file "help.mli";;
use_file "help.ml";;
open Help;;

use_file "banner.mli";;
use_file "banner.ml";;
open Banner;;

reset_step_counter ();;
print_banner ();;
