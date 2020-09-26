(* ========================================================================== *)
(* COMMON HOL API (HOL Light svn75 ++)                                        *)
(* - Interface for the Common HOL API version 0.4                             *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2011-2013                            *)
(* ========================================================================== *)


module CommonHOL : CommonHOL_sig = struct


(* This module defines the Common HOL API, giving portability of proofs and   *)
(* source code across HOL systems.  It provides functional programming        *)
(* utilities, HOL term/type utilities, theory commands, inference rules,      *)
(* theorems and pretty printer support.  It aims to capture the essence of    *)
(* basic HOL functionality, and each system in the HOL family implements a    *)
(* vast majority of its objects.                                              *)

(* HOL Zero is designed to implement all of the Common HOL API in its base    *)
(* system.  This module can thus be implemented simply by using module        *)
(* inclusion on existing modules.                                             *)


(* System parameters *)

let hol_system = "HOL Zero";;
let hol_version = holzero_version;;
let commonhol_version = "0.5";;


(* Module inclusion *)

include Exn;;
include Lib;;

include Type;;
include Term;;
include Thm;;
include CoreThry;;

include Names;;
include Parser;;
include Printer;;

include Utils1;;
include Utils2;;
include Wrap;;
include Store;;

include Def1;;
include Def2;;

include Equal;;
include EqCong;;
include Bool;;
include BoolAlg;;
include BoolClass;;
include Pair;;
include Ind;;
include Nat;;
include NatNumrl;;
include NatArith;;
include NatRel;;
include NatEval;;


end;;
