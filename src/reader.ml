(* ========================================================================== *)
(* READER LIBRARY (HOL Zero)                                                  *)
(* - Library of generic reader combinators                                    *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2015                            *)
(* ========================================================================== *)


module Reader : Reader_sig = struct


(* This module provides a library of generic reader combinators, for use in   *)
(* the implementation of recursive descent parsers.  These combinators act on *)
(* reader functions, that process data from a given source and return a read  *)
(* item and the source correspondingly advanced, ready for the next item to   *)
(* be read.  Basic combinators are provided that correspond to classic        *)
(* operators of BNF-style grammars, which allows parsers to be written in a   *)
(* way that transparently reflects the grammar that they are implementing.    *)

(* Some of the combinators are infix, with precedence and associativity that  *)
(* reflects their corresponding grammar operators.  Note that, in OCaml, the  *)
(* ML fixity of an identifier is determined purely by its name - see the      *)
(* table in Section 6.7 (The Objective Caml Language, Expressions) of the     *)
(* OCaml User Manual for the rules.  Thus the names of the combinators have   *)
(* to be carefully chosen to give the desired effect.                         *)



(* reader datatype *)

(* First we define a datatype for reader functions.  The first type parameter *)
(* is for the source type and second is for the item type.                    *)

type ('a,'b) reader = ('a -> 'b *'a);;


(* Read fail exception *)

(* This exception is dedicated to non-fatal failures in reader functions, and *)
(* is used for simple control flow between reader combinators.  This allows   *)
(* simple implementation of reader combinators that trap non-fatal failures   *)
(* and act accordingly, whilst allowing other exceptions to propagate.        *)

exception ReadFail;;



(* ** GENERIC SOURCE COMBINATORS ** *)

(* This section defines reader combinators with no restrictions on the form   *)
(* of the source.                                                             *)


(* Basic alternation combinator *)

(* ( ||| ) :  ('a,'b) reader -> ('a,'b) reader -> ('a,'b) reader              *)
(*                                                                            *)
(* This infix combinator is for alternation.  The LHS reader function is      *)
(* tried first, and if this produces a ReadFail then the RHS reader function  *)
(* is tried from the same starting point.                                     *)

let ( ||| ) read_fn1 read_fn2 src =
  try
    read_fn1 src
  with ReadFail ->
    read_fn2 src;;


(* Basic sequential combinators *)

(* ( >>> ) :  ('a,'b) reader -> ('a,'c) reader -> ('a,'b*'c) reader           *)
(* ( *>> ) :  ('a,'b) reader -> ('a,'c) reader -> ('a,'c) reader              *)
(* ( >>* ) :  ('a,'b) reader -> ('a,'c) reader -> ('a,'b) reader              *)
(*                                                                            *)
(* These infix combinators are for reading in sequence.  The LHS reader       *)
(* function reads an initial part, and the RHS reader function reads the next *)
(* part, with a ReadFail raised if either reader raises one.  The '>>>'       *)
(* combinator returns the combined results as a pair, whereas '*>>' discards  *)
(* the LHS result, and '>>*' discards the RHS result.                         *)

let ( >>> ) read_fn1 read_fn2 src =
  let (x1,src') = read_fn1 src in
  let (x2,src'') = read_fn2 src' in
  ((x1,x2),src'');;

let ( *>> ) read_fn1 read_fn2 src =
  let (x1,src') = read_fn1 src in
  let (x2,src'') = read_fn2 src' in
  (x2,src'');;

let ( >>* ) read_fn1 read_fn2 src =
  let (x1,src') = read_fn1 src in
  let (x2,src'') = read_fn2 src' in
  (x1,src'');;


(* Context-passing combinators *)

(* These combinators are for passing on the result of one reader function as  *)
(* context to another, either for efficient processing or error reporting.    *)

(* ( |@| ) : ('a,'b) reader -> ('b -> ('a,'b) reader) -> ('a,'b) reader       *)
(*                                                                            *)
(* This infix combinator is for alternation with a left factor, where the     *)
(* left factor forms the whole of one branch and the initial part of another  *)
(* branch.  The result of the LHS reader function can be used in both         *)
(* branches, thus avoiding the need for backtracking.                         *)

let ( |@| ) read_fn1 read_fn2 src =
  let (x1,src') = read_fn1 src in
  try
    let (x2,src'') = read_fn2 x1 src' in
    (x2,src'')
  with ReadFail ->
    (x1,src');;

(* ( >@> ) : ('a,'b) reader -> ('b -> ('a,'c) reader) -> ('a,'b*'c) reader    *)
(*                                                                            *)
(* For this infix combinator, the result of the LHS reader function forms     *)
(* part of the overall result, as well as being passed as context to the RHS  *)
(* reader function.  This is useful for error reporting.                      *)

let ( >@> ) read_fn1 read_fn2 src =
  let (x1,src') = read_fn1 src in
  let (x2,src'') = read_fn2 x1 src' in
  ((x1,x2),src'');;

(* ( *@> ) : ('a,'b) reader -> ('b -> ('a,'c) reader) -> ('a,'c) reader       *)
(*                                                                            *)
(* For this infix combinator, the result of the LHS reader function does not  *)
(* directly form part of overall result, but is passed as context to the RHS  *)
(* reader function.  This is useful for error reporting.                      *)

let ( *@> ) read_fn1 read_fn2 src =
  let (x1,src') = read_fn1 src in
  let (x2,src'') = read_fn2 x1 src' in
  (x2,src'');;


(* Reading a list *)

(* read_list : int -> ('a,'b) reader -> ('a, 'b list) reader                  *)
(*                                                                            *)
(* This combinator reads a variable-length sequence, of length at least 'n',  *)
(* using the supplied reader function for each element, and keeps going until *)
(* the reader gives a ReadFail, upon which it returns the successfully read   *)
(* elements as a list.                                                        *)

let rec read_list n read_fn src =
  try
    let (x1,src') = read_fn src in
    let (xs2,src'') = read_list (decrement n) read_fn src' in
    (x1::xs2, src'')
  with ReadFail ->
    if (n = 0) then ([],src)
               else raise ReadFail;;


(* Post processing *)

(* These don't correspond to grammar operators, but are for applying a        *)
(* function to the result of a given reader function, repackaging it into a   *)
(* suitable form.                                                             *)

(* ( @: ) : ('b -> 'c) -> ('a,'b) reader -> ('a,'c) reader                    *)
(*                                                                            *)
(* This infix combinator returns a reader function that uses its LHS to       *)
(* reformulate the result of its RHS reader function.                         *)

let ( @: ) f read_fn src =
  let (x,src') = read_fn src in
  (f x, src');;

(* ( @!: ) : ('b -> string) -> ('a,'b) reader -> 'a -> string                 *)
(*                                                                            *)
(* This infix function returns a string obtained by applying its LHS to the   *)
(* result of its RHS reader function.  This is useful when writing diagnosis  *)
(* functions.                                                                 *)

let ( @!: ) f read_fn src =
  let (x,src') = read_fn src in
  f x;;


(* Other generic reader combinators *)

(* lookahead : ('a,'b) reader -> ('a,'b) reader                               *)
(*                                                                            *)
(* This combinator uses the supplied reader function to read the next item,   *)
(* returning the read item but without advancing the source, and failing if   *)
(* the supplied reader fails.                                                 *)

let lookahead read_fn src =
  let (x,_) = read_fn src in
  (x,src);;

(* read_with : ('a,'b) reader -> ('b -> bool) -> ('a,'b) reader               *)
(*                                                                            *)
(* This combinator reads with the supplied reader function, but conditional   *)
(* upon the result satisfying the supplied test function.                     *)

let read_with read_fn test_fn src =
  let (x,src') = read_fn src in
  if (test_fn x)
    then (x,src')
    else raise ReadFail;;



(* ** LIST SOURCE COMBINATORS ** *)

(* This section defines support specialised for a source in the form of a     *)
(* list, whereby elements are read from the front of the list, leaving unread *)
(* elements in the remainder.                                                 *)


(* Head item readers *)

(* These are functions for reading the head item from a list source.          *)

let read_elem src =
  match src with
    e::src' -> (e,src')
  | _       -> raise ReadFail;;

let read_elem_with test_fn src =
  read_with read_elem test_fn src;;

let read_elem_in es src =
  let test_fn e = (mem e es) in
  read_elem_with test_fn src;;

let read_elem_not_in es src =
  let test_fn e = not (mem e es) in
  read_elem_with test_fn src;;


(* Start and end *)

(* These functions check that a list source respectively does and doesn't     *)
(* have remaining elements.                                                   *)

let read_start src =
  if (is_nonempty src)
    then ((), src)
    else raise ReadFail;;

let read_end src =
  if (is_empty src)
    then ((), src)
    else raise ReadFail;;


end;;
