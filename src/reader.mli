(* ========================================================================== *)
(* READER LIBRARY (HOL Zero)                                                  *)
(* - Library of generic reader combinators                                    *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2013                            *)
(* ========================================================================== *)


module type Reader_sig = sig

  (* Exceptions *)

  exception ReadFail

  (* Reader function datatype *)

  type ('a,'b) reader = ('a -> 'b * 'a)

  (* Generic source readers *)

  val ( @: ) : ('b -> 'c) -> ('a,'b) reader -> ('a,'c) reader
  val ( @!: ) : ('b -> string) -> ('a,'b) reader -> 'a -> string

  val ( ||| ) : ('a,'b) reader -> ('a,'b) reader -> ('a,'b) reader
  val ( >>> ) : ('a,'b) reader -> ('a,'c) reader -> ('a,'b*'c) reader
  val ( *>> ) : ('a,'b) reader -> ('a,'c) reader -> ('a,'c) reader
  val ( >>* ) : ('a,'b) reader -> ('a,'c) reader -> ('a,'b) reader
  val ( |@| ) : ('a,'b) reader -> ('b -> ('a,'b) reader) -> ('a,'b) reader
  val ( *@> ) : ('a,'b) reader -> ('b -> ('a,'c) reader) -> ('a,'c) reader
  val ( >@> ) : ('a,'b) reader -> ('b -> ('a,'c) reader) -> ('a,'b*'c) reader

  val read_list : int -> ('a,'b) reader -> ('a, 'b list) reader
  val lookahead : ('a,'b) reader -> ('a,'b) reader
  val read_with : ('a,'b) reader -> ('b -> bool) -> ('a,'b) reader

  (* List source readers *)

  val read_elem : ('a list, 'a) reader
  val read_elem_with : ('a -> bool) -> ('a list, 'a) reader
  val read_elem_in : 'a list -> ('a list, 'a) reader
  val read_elem_not_in : 'a list -> ('a list, 'a) reader
  val read_start : ('a list, unit) reader
  val read_end : ('a list, unit) reader

end;;
