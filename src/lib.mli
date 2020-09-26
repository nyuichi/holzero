(* ========================================================================== *)
(* LIBRARY (HOL Zero)                                                         *)
(* - Functional programming library                                           *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2016                            *)
(* ========================================================================== *)


module type Lib_sig = sig

  (* Exception handling *)

  val check : ('a -> bool) -> 'a -> 'a
  val assert0 : bool -> exn -> unit
  val assert1 : bool -> string * string -> unit
  val try0 : ('a -> 'b) -> 'a -> exn -> 'b
  val try1 : ('a -> 'b) -> 'a -> string * string -> 'b
  val try2 : ('a -> 'b) -> 'a -> string -> 'b

  val try_find : ('a -> 'b) -> 'a list -> 'b
  val try_filter : ('a -> 'b) -> 'a list -> 'b list
  val can : ('a -> 'b) -> 'a -> bool
  val cannot : ('a -> 'b) -> 'a -> bool
  val repeat : ('a -> 'a) -> 'a -> 'a

  (* Tuples *)

  val pair : 'a -> 'b -> 'a * 'b
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
  val switch : 'a * 'b -> 'b * 'a

  (* Lists *)

  val length : 'a list -> int
  val length_big_int : 'a list -> big_int
  val cons : 'a -> 'a list -> 'a list
  val is_empty : 'a list -> bool
  val is_nonempty : 'a list -> bool
  val hd : 'a list -> 'a
  val tl : 'a list -> 'a list
  val hd_tl : 'a list -> 'a * 'a list
  val front : 'a list -> 'a list
  val last : 'a list -> 'a
  val front_last : 'a list -> 'a list * 'a
  val el0 : int -> 'a list -> 'a
  val el : int -> 'a list -> 'a
  val append : 'a list -> 'a list -> 'a list
  val flatten : 'a list list -> 'a list
  val rev : 'a list -> 'a list
  val copy : int -> 'a -> 'a list
  val cut : int -> 'a list -> 'a list * 'a list
  val cut_big_int : big_int -> 'a list -> 'a list * 'a list
  val cut_while : ('a -> bool) -> 'a list -> 'a list * 'a list
  val list_eq : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool

  (* Integers *)

  val decrement : int -> int
  val up_to : int -> int -> int list

  (* Combinatory logic *)

  val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
  val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
  val apply : ('a -> 'b) -> 'a -> 'b
  val id_fn : 'a -> 'a
  val con_fn : 'a -> 'b -> 'a
  val (<*) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
  val funpow : int -> ('a -> 'a) -> 'a -> 'a
  val swap_arg : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val dbl_arg : ('a -> 'a -> 'b) -> 'a -> 'b

  (* Meta functions *)

  val pair_apply : ('a -> 'b) * ('c -> 'd) -> 'a * 'c -> 'b * 'd
  val map : ('a -> 'b) -> 'a list -> 'b list
  val bimap : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list

  val foldl : ('b -> 'a -> 'b) -> 'b -> 'a list -> 'b
  val foldr : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val foldl1 : ('a -> 'a -> 'a) -> 'a list -> 'a
  val foldr1 : ('a -> 'a -> 'a) -> 'a list -> 'a

  val foldl' : ('b * 'a -> 'b) -> 'b * 'a list -> 'b
  val foldr' : ('a * 'b -> 'b) -> 'a list * 'b -> 'b
  val foldl1' : ('a * 'a -> 'a) -> 'a list -> 'a
  val foldr1' : ('a * 'a -> 'a) -> 'a list -> 'a

  val unfoldl : ('a -> 'a * 'b) -> 'a -> 'a * 'b list
  val unfoldr : ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  val unfoldl1 : ('a -> 'a * 'a) -> 'a -> 'a list
  val unfoldr1 : ('a -> 'a * 'a) -> 'a -> 'a list
  val unfold : ('a -> 'a * 'a) -> 'a -> 'a list

  (* Test functions *)

  val find : ('a -> bool) -> 'a list -> 'a
  val filter : ('a -> bool) -> 'a list -> 'a list
  val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
  val exists : ('a -> bool) -> 'a list -> bool
  val forall : ('a -> bool) -> 'a list -> bool

  (* Association lists *)

  val enumerate : 'a list -> (int * 'a) list
  val zip : 'a list -> 'b list -> ('a * 'b) list
  val unzip : ('a * 'b) list -> 'a list * 'b list
  val assoc : 'a -> ('a * 'b) list -> 'b
  val inv_assoc : 'b -> ('a * 'b) list -> 'a
  val fst_map : ('a -> 'c) -> ('a * 'b) list -> ('c * 'b) list
  val snd_map : ('b -> 'c) -> ('a * 'b) list -> ('a * 'c) list
  val fst_filter : ('a -> bool) -> ('a * 'b) list -> ('a * 'b) list
  val snd_filter : ('b -> bool) -> ('a * 'b) list -> ('a * 'b) list

  (* Unit-valued functions *)

  val do_map : ('a -> unit) -> 'a list -> unit

  (* Unordered sets *)

  val setify : 'a list -> 'a list
  val mem : 'a -> 'a list -> bool
  val insert : 'a -> 'a list -> 'a list
  val union : 'a list -> 'a list -> 'a list
  val unions : 'a list list -> 'a list
  val intersect : 'a list -> 'a list -> 'a list
  val subtract : 'a list -> 'a list -> 'a list
  val subset : 'a list -> 'a list -> bool
  val disjoint : 'a list -> 'a list -> bool
  val set_eq : 'a list -> 'a list -> bool
  val no_dups : 'a list -> bool

  val setify' : ('a->'a->bool) -> 'a list -> 'a list
  val mem' : ('a->'a->bool) -> 'a -> 'a list -> bool
  val insert' : ('a->'a->bool) -> 'a -> 'a list -> 'a list
  val union' : ('a->'a->bool) -> 'a list -> 'a list -> 'a list
  val unions' : ('a->'a->bool) -> 'a list list -> 'a list
  val intersect' : ('a->'a->bool) -> 'a list -> 'a list -> 'a list
  val subtract' : ('a->'a->bool) -> 'a list -> 'a list -> 'a list
  val subset' : ('a->'a->bool) -> 'a list -> 'a list -> bool
  val disjoint' : ('a->'a->bool) -> 'a list -> 'a list -> bool
  val set_eq' : ('a->'a->bool) -> 'a list -> 'a list -> bool
  val no_dups' : ('a->'a->bool) -> 'a list -> bool

  (* Characters and strings *)

  val implode : string list -> string
  val explode : string -> string list
  val char_implode : char list -> string
  val char_explode : string -> char list
  val int_of_string : string -> int
  val string_of_int : int -> string
  val string_variant : string list -> string -> string
  val quote0 : string -> string
  val quote : string -> string

  (* Reporting *)

  val report : string -> unit
  val warn : string -> unit

  (* Sorting *)

  val merge : ('a->'a->bool) -> 'a list -> 'a list -> 'a list
  val mergesort : ('a->'a->bool) -> 'a list -> 'a list

end;;
