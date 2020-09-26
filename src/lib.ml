(* ========================================================================== *)
(* LIBRARY (HOL Zero)                                                         *)
(* - Functional programming library                                           *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2016                            *)
(* ========================================================================== *)


module Lib : Lib_sig = struct


(* This module defines various generic functional programming utilities.      *)



(* ** EXCEPTION HANDLING ** *)

(* This section defines various supporting functions for exceptions,          *)
(* concentrating on HolFail exceptions.                                       *)


(* check : ('a -> bool) -> 'a -> 'a                                           *)
(*                                                                            *)
(* Raises a HolFail exception if the supplied argument does not satisfy the   *)
(* supplied test function, otherwise returning the argument.                  *)

let check p x =
  if (p x) then x
           else hol_fail ("check","Test fails");;


(* assert0 : bool -> exn -> unit                                              *)
(*                                                                            *)
(* Raises the supplied exception if the supplied boolean is "false",          *)
(* otherwise returning unit.                                                  *)

let assert0 b e =
  if not b then raise e;;


(* assert1 : bool -> string * string -> unit                                  *)
(*                                                                            *)
(* Raises a HolFail exception for the supplied function name and message if   *)
(* the supplied boolean is "false", and otherwise returns unit.               *)

let assert1 b (func,msg) =
  if not b then hol_fail (func,msg);;


(* try0 : ('a -> 'b) -> 'a -> exn -> 'b                                       *)
(*                                                                            *)
(* Applies the supplied function to the supplied argument, and if this causes *)
(* a HolFail exception then catches this and raises the supplied exception    *)
(* instead.                                                                   *)

let try0 f x e =
  try
    f x
  with HolFail _ -> raise e;;


(* try1 : ('a -> 'b) -> 'a -> string * string -> 'b                           *)
(*                                                                            *)
(* Applies the supplied function to the supplied argument, and if this causes *)
(* a HolFail exception then catches this and raises a HolFail exception with  *)
(* the supplied function name and message instead.                            *)

let try1 f x (func,msg) =
  try
    f x
  with HolFail _ -> hol_fail (func,msg);;


(* try2 : ('a -> 'b) -> 'a -> string -> 'b                                    *)
(*                                                                            *)
(* Applies the supplied function to the supplied argument, and if this causes *)
(* a HolFail exception then catches this and reraises the HolFail with the    *)
(* same message but for the supplied function name.                           *)

let try2 f x func =
  try
    f x
  with HolFail (_,msg) -> hol_fail (func,msg);;


(* try_find : ('a -> 'b) -> 'a list -> 'b                                     *)
(*                                                                            *)
(* Applies the supplied function to the first item of the supplied list that  *)
(* doesn't cause a HolFail exception.  Fails if there is no such list item.   *)

let rec try_find f xs =
  match xs with
    x0::xs0 -> (try f x0
                with HolFail _ -> try_find f xs0)
  | []      -> hol_fail ("try_find","No successful application");;


(* try_filter : ('a -> 'b) -> 'a list -> 'b list                              *)
(*                                                                            *)
(* Applies the supplied function to those items of the supplied list that     *)
(* don't cause a HolFail exception, and removing items that do.               *)

let rec try_filter f xs =
  match xs with
    x0::xs0 -> let ys0 = try_filter f xs0 in
               (try (f x0)::ys0
                with HolFail _ -> ys0)
  | []      -> [];;


(* can : ('a -> 'b) -> 'a -> bool                                             *)
(* cannot : ('a -> 'b) -> 'a -> bool                                          *)
(*                                                                            *)
(* Returns "true" iff applying the supplied function to the supplied argument *)
(* respectively doesn't or does cause a HolFail exception.                    *)

let can f x =
  try
    let _ = f x in
    true
  with HolFail _ ->
    false;;

let cannot f x = not (can f x);;


(* repeat : ('a -> 'a) -> 'a -> 'a                                            *)
(*                                                                            *)
(* Repeatedly applies the supplied function to an argument until it causes a  *)
(* HolFail exception, returning the manifestation of the argument that causes *)
(* the exception.  Note that this will not terminate if the function never    *)
(* raises an exception.                                                       *)

let rec repeat f x =
  try
    let y = f x in
    repeat f y
  with HolFail _ ->
    x;;



(* ** TUPLES ** *)

(* This section is for functions that perform basic manipulations on tuples.  *)


(* fst : 'a * 'b -> 'a                                                        *)
(* snd : 'a * 'b -> 'b                                                        *)
(*                                                                            *)
(* Respectively select the first and second components of a pair.             *)

let fst = Pervasives.fst;;
let snd = Pervasives.snd;;


(* pair : 'a -> 'b -> 'a * 'b                                                 *)
(*                                                                            *)
(* The curried binary operator for constructing pairs.                        *)

let pair x y = (x,y);;


(* switch : 'a * 'b -> 'b * 'a                                                *)
(*                                                                            *)
(* Switches around the two components of a given pair.                        *)

let switch (x,y) = (y,x);;



(* ** LISTS ** *)

(* This section is for functions that perform basic manipulations on lists.   *)


(* length : 'a list -> int                                                    *)
(*                                                                            *)
(* Returns the length of the supplied list.                                   *)

let rec length0 n xs =
  match xs with
    _::xs0 -> length0 (n+1) xs0
  | []     -> n;;

let length xs = length0 0 xs;;

let rec length_big_int0 n xs =
  match xs with
    _::xs0 -> length_big_int0 (add_big_int n big_int_1) xs0
  | []     -> n;;

let length_big_int xs = length_big_int0 big_int_0 xs;;


(* cons : 'a -> 'a list -> 'a list                                            *)
(*                                                                            *)
(* Adds a given item to the start of a given list.  The nonfix curried form   *)
(* of '::'.                                                                   *)

let cons x xs = x::xs;;


(* is_empty : 'a list -> bool                                                 *)
(* is_nonempty : 'a list -> bool                                              *)
(*                                                                            *)
(* Returns "true" iff the supplied list is empty or nonempty respectively.    *)

let is_empty xs =
  match xs with
    [] -> true
  | _  -> false;;

let is_nonempty xs =
  match xs with
    [] -> false
  | _  -> true;;


(* hd : 'a list -> 'a                                                         *)
(* tl : 'a list -> 'a list                                                    *)
(* hd_tl : 'a list -> 'a * 'a list                                            *)
(*                                                                            *)
(* Functions for destructing a supplied list into its head item and its tail  *)
(* items.  These fail if the list is empty.                                   *)

let hd xs =
  match xs with
    x0::_ -> x0
  | _     -> hol_fail ("hd","Empty list");;

let tl xs =
  match xs with
    _::xs0 -> xs0
  | _      -> hol_fail ("tl","Empty list");;

let hd_tl xs =
  match xs with
    x0::xs0 -> (x0,xs0)
  | _       -> hol_fail ("hd_tl","Empty list");;


(* front : 'a list -> 'a list                                                 *)
(* last : 'a list -> 'a                                                       *)
(* front_last : 'a list -> 'a list * 'a                                       *)
(*                                                                            *)
(* Functions for destructing a supplied list into its front items and its     *)
(* last item.  These fail if the list is empty.                               *)

let rec front xs =
  match xs with
    _::[]   -> []
  | x0::xs0 -> x0::(front xs0)
  | []      -> hol_fail ("front","Empty list");;

let rec last xs =
  match xs with
    x0::[] -> x0
  | _::xs0 -> last xs0
  | []     -> hol_fail ("last","Empty list");;

let front_last xs =
 try
  (front xs, last xs)
 with HolFail _ -> hol_fail ("front_last","Empty list");;


(* list_eq : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool                 *)
(*                                                                            *)
(* Returns "true" iff the two inputted lists are equivalent modulo the        *)
(* supplied equivalence relation 'eq', i.e. the lists have equal length and   *)
(* corresponding elements are equal modulo 'eq'.                              *)

let rec list_eq eq xs ys =
  match (xs,ys) with
    (x0::xs0, y0::ys0) -> (eq x0 y0) && (list_eq eq xs0 ys0)
  | ([]     , []     ) -> true
  | _                  -> false;;


(* rev : 'a list -> 'a list                                                   *)
(*                                                                            *)
(* Reverses the order of the items in the supplied list.                      *)

let rec rev0 ys xs =
  match xs with
    x0::xs0 -> rev0 (x0::ys) xs0
  | []      -> ys;;

let rev xs = rev0 [] xs;;


(* copy : int -> 'a -> 'a list                                                *)
(*                                                                            *)
(* Produces a list composed of the supplied element copied the supplied       *)
(* number of times.                                                           *)

let rec copy0 n x xs0 =
  if (n < 1)
    then xs0
    else copy0 (n-1) x (x::xs0);;

let copy n x = copy0 n x [];;


(* append : 'a list -> 'a list -> 'a list                                     *)
(*                                                                            *)
(* Joins the two supplied lists together.  The nonfix curried form of '@'.    *)

let append xs ys = xs @ ys;;


(* flatten : 'a list list -> 'a list                                          *)
(*                                                                            *)
(* Flattens the supplied list of lists into a single list.                    *)

let rec flatten xss =
  match xss with
    xs0::xss0 -> xs0 @ (flatten xss0)
  | []        -> [];;


(* zip : 'a list -> 'b list -> ('a * 'b) list                                 *)
(*                                                                            *)
(* Combines corresponding items of the two supplied lists into pairs.  Fails  *)
(* if the lists do not have the same length.                                  *)

let rec zip xs ys =
  match (xs,ys) with
    (x0::xs0,y0::ys0) -> (x0,y0)::(zip xs0 ys0)
  | ([],[])           -> []
  | _                 -> hol_fail ("zip","Lists of unequal length");;


(* unzip : ('a * 'b) list -> 'a list * 'b list                                *)
(*                                                                            *)
(* Splits up the supplied list of pairs into the list of the first components *)
(* and the list of the second components of each pair.                        *)

let rec unzip xys =
  match xys with
    (x0,y0)::xys0 -> let (xs0,ys0) = unzip xys0 in
                     (x0::xs0,y0::ys0)
  | _             -> ([],[]);;


(* el : int -> 'a list -> 'a                                                  *)
(*                                                                            *)
(* Returns the nth item of the supplied list, using 1-based indexing.  Fails  *)
(* if the index is out of range.                                              *)

let rec el1 n xs =
  match xs with
    x0::xs1 -> if (n > 1) then el1 (n-1) xs1
                          else x0
  | []      -> hol_fail ("el","Index too big");;

let el n xs =
  if (n >= 1)
    then el1 n xs
    else hol_fail ("el","Index not positive");;


(* el0 : int -> 'a list -> 'a                                                 *)
(*                                                                            *)
(* Returns the nth item of the supplied list, using 0-based indexing.  Fails  *)
(* if the index is out of range.                                              *)

let el0 n xs =
  if (n >= 0)
    then try2 (el1 (n+1)) xs "el0"
    else hol_fail ("el0","Index negative");;


(* cut : int -> 'a list -> 'a list * 'a list                                  *)
(*                                                                            *)
(* Cuts the supplied list into two according to 1-based index 'n', with items *)
(* 1 up to 'n' in the first list and the remaining in the second.  Fails if   *)
(* 'n' is negative or greater than the list's length.                         *)

let rec cut n xs =
  if (n > 0)
    then match xs with
           x0::xs0 -> let (ys,zs) = cut (n-1) xs0 in
                      (x0::ys,zs)
         | _       -> hol_fail ("cut","Index larger than list length")
  else if (n = 0)
    then ([], xs)
    else hol_fail ("cut","Negative index");;

let rec cut_big_int n xs =
  if (gt_big_int n big_int_0)
    then match xs with
           x0::xs0 -> let (ys,zs) = cut_big_int (sub_big_int n big_int_1) xs0 in
                      (x0::ys,zs)
         | _       -> hol_fail ("cut","Index larger than list length")
  else if (eq_big_int n big_int_0)
    then ([], xs)
    else hol_fail ("cut_big_int","Negative index");;


(* cut_while : ('a -> bool) -> 'a list -> 'a list * 'a list                   *)
(*                                                                            *)
(* Cuts the supplied list into two segments, with the second segment starting *)
(* at the first item not satisfying the supplied test function.               *)

let rec cut_while0 p ys xs =
  match xs with
    x0::xs0 -> if (p x0)
                 then cut_while0 p (x0::ys) xs0
                 else (ys, xs)
  | []      -> (ys, xs);;

let cut_while p xs =
  let (ys,zs) = cut_while0 p [] xs in
  (rev ys, zs);;



(* ** INTEGERS ** *)

(* This section is for functions that perform basic integer operations.       *)


(* decrement : int -> int                                                     *)
(*                                                                            *)
(* Subtracts 1 if the supplied integer is positive, otherwise returns 0.      *)

let decrement n = if (n > 0) then n-1 else 0;;


(* up_to : int -> int -> int list                                             *)
(*                                                                            *)
(* Returns the contiguous increasing list of integers ranging from the first  *)
(* supplied integer to the second.  Returns an empty list if the second       *)
(* argument is less than the first.                                           *)

let rec up_to0 m n ns0 =
  if (m <= n)
    then up_to0 m (n-1) (n::ns0)
    else ns0;;

let rec up_to m n = up_to0 m n [];;



(* ** COMBINATORY LOGIC ** *)

(* This section defines some classic functions from combinatory logic.        *)


(* curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c                                  *)
(*                                                                            *)
(* Returns the curried equivalent of a given tupled binary function.          *)

let curry f x y = f (x,y);;


(* uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c                                *)
(*                                                                            *)
(* Returns the tupled equivalent of the supplied curried binary function.     *)

let uncurry f (x,y) = f x y;;


(* apply : ('a -> 'b) -> 'a -> 'b                                             *)
(*                                                                            *)
(* The function that applies its first argument to its second, returning the  *)
(* result.  Called the 'A' combinator in combinatory logic.                   *)

let apply f x = f x;;


(* id_fn : 'a -> 'a                                                           *)
(*                                                                            *)
(* The function that returns its argument as its result.  Called the 'I'      *)
(* combinator in combinatory logic.                                           *)

let id_fn x = x;;


(* con_fn : 'a -> 'b -> 'a                                                    *)
(*                                                                            *)
(* The curried binary function that returns its first argument.  Called the   *)
(* 'K' combinator in combinatory logic.                                       *)

let con_fn x y = x;;


(* ( <* ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b                              *)
(*                                                                            *)
(* The infix binary function for function composition.  Called the 'B'        *)
(* combinator in combinatory logic.                                           *)

let ( <* ) f g = fun x -> f (g x);;


(* funpow : int -> ('a -> 'a) -> 'a -> 'a                                     *)
(*                                                                            *)
(* Applies the nth-power of the supplied function, i.e. recurses the function *)
(* n times, feeding the result back into the input, and returning the         *)
(* original input if n is 0.  Fails if the power is negative.                 *)

let rec funpow n f x =
  if (n > 0)
    then funpow (n-1) f (f x)
  else if (n = 0)
    then x
    else hol_fail ("funpow","Negative power");;


(* swap_arg : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c                              *)
(*                                                                            *)
(* Takes a curried binary function, and returns an equivalent function that   *)
(* takes its arguments in opposite order.  Called the 'C' combinator in       *)
(* combinatory logic.                                                         *)

let swap_arg f x y = f y x;;


(* dbl_arg : ('a -> 'a -> 'b) -> 'a -> 'b                                     *)
(*                                                                            *)
(* Applies the supplied curried binary function using the supplied argument   *)
(* for both arguments of the function.  Called the 'W' combinator in          *)
(* combinatory logic.                                                         *)

let dbl_arg f x = f x x;;



(* ** META FUNCTIONS ** *)

(* This section is for functions that take function arguments and apply them  *)
(* over pair or list structures.                                              *)


(* pair_apply : ('a -> 'b) * ('c -> 'd) -> 'a * 'c -> 'b * 'd                 *)
(*                                                                            *)
(* Applies supplied pair of functions to corresponding components of a given  *)
(* pair.                                                                      *)

let pair_apply (f,g) (x,y) = (f x, g y);;


(* map :  ('a -> 'b) -> 'a list -> 'b list                                    *)
(*                                                                            *)
(* Applies the supplied function to each item of the supplied list.           *)
(*                                                                            *)
(*    map f [x1;x2;..;xn]  ==  [f x1; f x2; ..; f xn]                         *)

let rec map f xs =
  match xs with
    x0::xs0 -> let y = f x0 in
               y::(map f xs0)
  | []      -> [];;


(* bimap : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list                  *)
(*                                                                            *)
(* Applies a given curried binary function to corresponding items of two      *)
(* given lists.  Fails if the lists don't have the same length.               *)
(*                                                                            *)
(*    bimap (+) [x1;x2;..;xn] [y1;y2;..;yn] = [x1 + y1; x2 + y2; ..; xn + yn] *)

let rec bimap f xs ys =
  match (xs,ys) with
    (x0::xs0, y0::ys0)
            -> let z = f x0 y0 in
               z::(bimap f xs0 ys0)
  | ([],[]) -> []
  | _       -> hol_fail ("bimap","Lists of unequal length");;


(* foldl : ('b -> 'a -> 'b) -> 'b -> 'a list -> 'b                            *)
(*                                                                            *)
(* Applies the supplied curried binary operator over the items of the         *)
(* supplied list, from left to right, starting with the operator applied to   *)
(* the supplied extra argument and the first item of the list.  Returns the   *)
(* extra argument if the list is empty.                                       *)
(*                                                                            *)
(*    foldl (+) a [x1;x2;..;xn]  ==  (..((a + x1) + x2) + ..) + xn            *)

let rec foldl f a xs =
  match xs with
    x1::xs2 -> foldl f (f a x1) xs2
  | []      -> a;;


(* foldl1 : ('a -> 'a -> 'a) -> 'a list -> 'a                                 *)
(*                                                                            *)
(* Applies the supplied curried binary operator over the items of the         *)
(* supplied list, from left to right.  Fails if the list is empty.            *)
(*                                                                            *)
(*    foldl1 (+) [x1;x2;..;xn]  ==  (..(x1 + x2) + ..) + xn                   *)

let rec foldl1 f xs =
  match xs with
    x1::xs2 -> foldl f x1 xs2
  | []      -> hol_fail ("foldl1","Empty list");;


(* foldr : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b                            *)
(*                                                                            *)
(* Applies the supplied curried binary operator over the items of the         *)
(* supplied list, from right to left, starting with the operator applied to   *)
(* the last item of the list and the supplied extra argument.  Returns the    *)
(* extra argument if the list is empty.                                       *)
(*                                                                            *)
(*    foldr (+) [x1;x2;..;xn] a  ==  x1 + (x2 + (.. + (xn + a)..))            *)

let rec foldr f xs a =
  match xs with
    x1::xs2 -> f x1 (foldr f xs2 a)
  | []      -> a;;


(* foldr1 : ('a -> 'a -> 'a) -> 'a list -> 'a                                 *)
(*                                                                            *)
(* Applies a given curried binary operator over the items of the supplied     *)
(* list, from right to left.  Fails if the list is empty.                     *)
(*                                                                            *)
(*    foldr1 (+) [x1;x2;..;xn]  ==  x1 + (x2 + .. + (xn-1 + xn)..)            *)

let rec foldr1 f xs =
  match xs with
    x::[]   -> x
  | x1::xs2 -> f x1 (foldr1 f xs2)
  | []      -> hol_fail ("foldr1","Empty list");;


(* Alternative fold operators *)

(* These are trivial variants of the above classic fold opertors, more suited *)
(* to implementing HOL syntax functions (which are uncurried).                *)

let foldl' mk_fn (x,xs) = foldl (curry mk_fn) x xs;;

let foldr' mk_fn (xs,x) = foldr (curry mk_fn) xs x;;

let foldl1' mk_fn xs = foldl1 (curry mk_fn) xs;;

let foldr1' mk_fn xs = foldr1 (curry mk_fn) xs;;


(* unfoldl : ('a -> 'a * 'b) -> 'a -> 'a * 'b list                            *)
(*                                                                            *)
(* Uses a given binary destructor to repeatedly destruct the LHS branch of    *)
(* the supplied argument until the destructor causes a HolFail exception.     *)
(* Returns the innermost LHS paired with the list of RHSs.                    *)

let rec unfoldl0 dest_fn x xs =
  try
    let (x1,x2) = dest_fn x in
    unfoldl0 dest_fn x1 (x2::xs)
  with HolFail _ -> (x,xs);;

let unfoldl dest_fn x = unfoldl0 dest_fn x [];;


(* unfoldl1 : ('a -> 'a * 'a) -> 'a -> 'a list                                *)
(*                                                                            *)
(* Uses a given binary destructor to repeatedly destruct the LHS branch of    *)
(* the supplied argument until the destructor causes a HolFail exception.     *)
(* Returns the list starting with innermost LHS followed by the RHSs.         *)

let unfoldl1 dest_fn x =
  let (x,xs) = unfoldl dest_fn x in
  x::xs;;


(* unfoldr : ('a -> 'b * 'a) -> 'a -> 'b list * 'a                            *)
(*                                                                            *)
(* Uses a given binary destructor to repeatedly destruct the RHS branch of    *)
(* the supplied argument until the destructor causes a HolFail exception.     *)
(* Returns the list of LHSs, paired with the innermost RHS.                   *)

let rec unfoldr0 dest_fn xs x =
  try
    let (x1,x2) = dest_fn x in
    unfoldr0 dest_fn (x1::xs) x2
  with HolFail _ -> (xs,x);;

let unfoldr dest_fn x =
  let (xs,x) = unfoldr0 dest_fn [] x in
  (rev xs, x);;


(* unfoldr1 : ('a -> 'a * 'a) -> 'a -> 'a list                                *)
(*                                                                            *)
(* Uses a given binary destructor to repeatedly destruct the RHS branch of    *)
(* the supplied argument until the destructor causes a HolFail exception.     *)
(* Returns the list of the LHSs and ending with the innermost RHS.            *)

let unfoldr1 dest_fn x =
  let (xs,x) = unfoldr0 dest_fn [] x in
  rev (x::xs);;


(* unfold : ('a -> 'a * 'a) -> 'a -> 'a list                                  *)
(*                                                                            *)
(* Uses a given binary destructor to repeatedly destruct all branches of the  *)
(* supplied argument until the destructor causes a HolFail excepton on each   *)
(* subbranch.  Returns a flattened list of the resulting tips.                *)

let rec unfold0 dest_fn x xs =
  try
    let (x1,x2) = dest_fn x in
    unfold0 dest_fn x1 (unfold0 dest_fn x2 xs)
  with HolFail _ -> x::xs;;

let unfold dest_fn x = unfold0 dest_fn x [];;



(* ** TEST FUNCTIONS ** *)

(* This section is for functions that take a test function (i.e. a function   *)
(* that returns a boolean) as an argument.                                    *)


(* find : ('a -> bool) -> 'a list -> 'a                                       *)
(*                                                                            *)
(* Returns the first item of the supplied list satisfying a given test        *)
(* function.  Fails if no such item exists.                                   *)

let rec find p xs =
  match xs with
    x0::xs0 -> if (p x0) then x0
                         else find p xs0
  | []      -> hol_fail ("find","No match");;


(* filter : ('a -> bool) -> 'a list -> 'a list                                *)
(*                                                                            *)
(* Removes all items of the supplied list not satisfying a given test         *)
(* function.                                                                  *)

let rec filter p xs =
  match xs with
    x0::xs0 -> if (p x0) then x0::(filter p xs0)
                         else filter p xs0
  | []      -> [];;


(* partition : ('a -> bool) -> 'a list -> 'a list * 'a list                   *)
(*                                                                            *)
(* Separates the supplied list into two lists, for those items respectively   *)
(* satisfying and not satisfying a given test function.                       *)

let rec partition p xs =
  match xs with
    x0::xs0 -> let (ys,zs) = partition p xs0 in
               if (p x0) then (x0::ys, zs)
                         else (ys, x0::zs)
  | []      -> ([], []);;


(* exists : ('a -> bool) -> 'a list -> bool                                   *)
(*                                                                            *)
(* Returns "true" iff there is at least one item in the supplied list         *)
(* satisfying a given test function.                                          *)

let rec exists p xs =
  match xs with
    x0::xs0 -> (p x0) || (exists p xs0)
  | []      -> false;;


(* forall : ('a -> bool) -> 'a list -> bool                                   *)
(*                                                                            *)
(* Returns "true" iff every item in the supplied list satisfies a given test  *)
(* function.                                                                  *)

let rec forall p xs =
  match xs with
    x0::xs0 -> (p x0) && (forall p xs0)
  | []      -> true;;



(* ** ASSOCIATION LISTS ** *)

(* This section is for functions that operate on association lists.  An       *)
(* association list is very simple representation of a lookup table as a list *)
(* of pairs.  Equality comparison under the OCaml '=' operator is used for    *)
(* comparing indexes.  Entries are added to and looked up from the front of   *)
(* the list, and multiple entries under the same index are allowed.  Either   *)
(* the left or right component of a pair can be used as the index key.        *)


(* assoc : 'a -> ('a * 'b) list -> 'b                                         *)
(* inv_assoc : 'b -> ('a * 'b) list -> 'a                                     *)
(*                                                                            *)
(* Respectively returns the right/left component of the first pair in the     *)
(* supplied list whose left/right component equals the supplied value.  Fails *)
(* if cannot find such a pair.                                                *)

let rec assoc x xys =
  match xys with
    (x0,y0)::xys0 -> if (x = x0) then y0
                                 else assoc x xys0
  | []            -> hol_fail ("assoc","No match");;

let rec inv_assoc y xys =
  match xys with
    (x0,y0)::xys0 -> if (y = y0) then x0
                                 else inv_assoc y xys0
  | []            -> hol_fail ("inv_assoc","No match");;


(* fst_map : ('a -> 'c) -> ('a * 'b) list -> ('c * 'b) list                   *)
(* snd_map : ('b -> 'c) -> ('a * 'b) list -> ('a * 'c) list                   *)
(*                                                                            *)
(* Applies the supplied function respectively to the left or right component  *)
(* of each pair in the supplied list of pairs.                                *)

let fst_map f xys = map (fun (x,y) -> (f x, y)) xys;;

let snd_map f xys = map (fun (x,y) -> (x, f y)) xys;;


(* fst_filter : ('a -> bool) -> ('a * 'b) list -> ('a * 'b) list              *)
(* snd_filter : ('b -> bool) -> ('a * 'b) list -> ('a * 'b) list              *)
(*                                                                            *)
(* Removes all items from the supplied association list that, respectively,   *)
(* have a left or right component that does not satisfy the supplied test     *)
(* function.                                                                  *)

let fst_filter p xys = filter (fun (x,y) -> p x) xys;;

let snd_filter p xys = filter (fun (x,y) -> p y) xys;;


(* enumerate : 'a list -> (int * 'a) list                                     *)
(*                                                                            *)
(* Turns the supplied list into an association list, where each item is       *)
(* indexed by its 1-based position in the list.                               *)

let rec enumerate0 n xs =
  match xs with
    x0::xs1 -> (n,x0)::(enumerate0 (n+1) xs1)
  | []      -> [];;

let enumerate xs = enumerate0 1 xs;;



(* ** UNIT-VALUED FUNCTIONS ** *)

(* This section is for functions that operate using unit-valued functions.    *)


(* do_map : ('a -> unit) -> 'a list -> unit                                   *)
(*                                                                            *)
(* Applies the supplied unit-valued function in turn to each item of the      *)
(* supplied list, returning unit.                                             *)

let rec do_map f xs =
  match xs with
    x0::xs0 -> (f x0; do_map f xs0)
  | []      -> ();;



(* ** UNORDERED SETS ** *)

(* This section is for functions that perform set-like operations on lists,   *)
(* where operations work modulo the set of items that occur in a list.        *)
(* Nothing, such as the order of list items or whether there are repeats, is  *)
(* assumed about the input lists, but if an input does have repeated items,   *)
(* then the output may also.                                                  *)

(* Two versions of each operation are defined: one where items are considered *)
(* equal wrt classic ML equality, and one where items are considered equal    *)
(* wrt a supplied equality-operator argument.                                 *)


(* mem : 'a -> 'a list -> bool                                                *)
(* mem' : ('a -> 'b -> bool) -> 'a -> 'b list -> bool                         *)
(*                                                                            *)
(* Returns "true" iff the supplied item is in the supplied list.              *)

let rec mem x xs =
  match xs with
    x0::xs0 -> (x = x0) || (mem x xs0)
  | []      -> false;;

let rec mem' eq x xs =
  match xs with
    x0::xs0 -> (eq x x0) || (mem' eq x xs0)
  | []      -> false;;


(* insert : 'a -> 'a list -> 'a list                                          *)
(* insert' : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list                   *)
(*                                                                            *)
(* Adds the supplied item to the supplied list unless it is already in the    *)
(* list.                                                                      *)

let insert x xs =
  if (mem x xs)
    then xs
    else x::xs;;

let insert' eq x xs =
  if (mem' eq x xs)
    then xs
    else x::xs;;


(* setify : 'a list -> 'a list                                                *)
(* setify' : ('a -> 'a -> bool) -> 'a list -> 'a list                         *)
(*                                                                            *)
(* Removes any duplicate items from the supplied list.                        *)

let setify xs = rev (foldl (swap_arg insert) [] xs);;

let setify' eq xs = rev (foldl (swap_arg (insert' eq)) [] xs);;


(* union : 'a list -> 'a list -> 'a list                                      *)
(* union' : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list               *)
(*                                                                            *)
(* Creates a list of items that occur in either of the two supplied lists.    *)

let union xs1 xs2 = foldr insert xs1 xs2;;

let union' eq xs1 xs2 = foldr (insert' eq) xs1 xs2;;


(* unions : 'a list list -> 'a list                                           *)
(* unions' : ('a -> 'a -> bool) -> 'a list list -> 'a list                    *)
(*                                                                            *)
(* Creates a list of items that occur in any list in the supplied list of     *)
(* lists.                                                                     *)

let unions xss =
  match xss with
    [] -> []
  | _  -> foldl1 union xss;;

let unions' eq xss =
  match xss with
    [] -> []
  | _  -> foldl1 (union' eq) xss;;


(* intersect : 'a list -> 'a list -> 'a list                                  *)
(* intersect' : ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list           *)
(*                                                                            *)
(* Creates a list of items that occur in both of the two supplied lists.      *)

let intersect xs1 xs2 = filter (fun x -> mem x xs2) xs1;;

let intersect' eq xs1 xs2 = filter (fun x -> mem' eq x xs2) xs1;;


(* subtract : 'a list -> 'a list -> 'a list                                   *)
(* subtract' : ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list            *)
(*                                                                            *)
(* Removes items from the first supplied list that also occur in the second.  *)

let subtract xs1 xs2 = filter (fun x1 -> not (mem x1 xs2)) xs1;;

let subtract' eq xs1 xs2 = filter (fun x1 -> not (mem' eq x1 xs2)) xs1;;


(* subset : 'a list -> 'a list -> bool                                        *)
(* subset' : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool                 *)
(*                                                                            *)
(* Returns "true" iff all items in the first supplied list also occur in the  *)
(* second.                                                                    *)

let subset xs1 xs2 = forall (fun x1 -> mem x1 xs2) xs1;;

let subset' eq xs1 xs2 = forall (fun x1 -> mem' eq x1 xs2) xs1;;


(* disjoint : 'a list -> 'a list -> bool                                      *)
(* disjoint' : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool               *)
(*                                                                            *)
(* Returns "true" iff there are no items common to both supplied lists.       *)

let rec disjoint xs ys =
  match (xs,ys) with
    (_     , []) -> true
  | (x::xs0, _ ) -> if (mem x ys)
                     then false
                     else disjoint xs0 ys
  | ([]    , _ ) -> true;;

let rec disjoint' eq xs ys =
  match (xs,ys) with
    (_     , []) -> true
  | (x::xs0, _ ) -> if (mem' eq x ys)
                     then false
                     else disjoint' eq xs0 ys
  | ([]    , _ ) -> true;;


(* set_eq : 'a list -> 'a list -> bool                                        *)
(* set_eq' : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool                 *)
(*                                                                            *)
(* Returns "true" iff the two supplied lists have the same items              *)
(* (disregarding duplicates).                                                 *)

let set_eq xs1 xs2 = (subset xs1 xs2) && (subset xs2 xs1);;

let set_eq' eq xs1 xs2 = (subset' eq xs1 xs2) && (subset' eq xs2 xs1);;


(* no_dups : 'a list -> bool                                                  *)
(* no_dups' : ('a->'a->bool) -> 'a list -> bool                               *)
(*                                                                            *)
(* Returns "true" iff the supplied list contains no duplicates.               *)

let rec no_dups0 xs0 xs =
  match xs with
    []      -> true
  | x1::xs2 -> not (mem x1 xs0) && (no_dups0 (x1::xs0) xs2);;

let no_dups xs = no_dups0 [] xs;;

let rec no_dups0' eq xs0 xs =
  match xs with
    []      -> true
  | x1::xs2 -> not (mem' eq x1 xs0) && (no_dups0' eq (x1::xs0) xs2);;

let no_dups' eq xs = no_dups0' eq [] xs;;




(* ** CHARACTERS AND STRINGS ** *)

(* This section is for functions that operate on characters or strings.       *)


(* string_of_int : int -> string                                              *)
(*                                                                            *)
(* Returns the string representation of the supplied integer.                 *)

let string_of_int = Pervasives.string_of_int;;


(* int_of_string : string -> int                                              *)
(*                                                                            *)
(* Returns the integer represented by the supplied string.  Disregards any    *)
(* '0' characters at the start of the string, and any '_' characters after    *)
(* the start of the string.  A single '-' character prefixed to the start of  *)
(* the string (without any separating spaces) signifies a negative number.    *)

let int_of_string x =
  try Pervasives.int_of_string x
  with Failure _ -> hol_fail ("int_of_string", "Not a valid integer string");;


(* char_implode : char list -> string                                         *)
(*                                                                            *)
(* Joins a list of characters into a single string.                           *)

let char_implode cs =
  let x = String.create (length cs) in
  let foo n c =
    let _ = String.set x n c in
    n + 1 in
  let _ = foldl foo 0 cs in
  x;;


(* char_explode : string -> char list                                         *)
(*                                                                            *)
(* Breaks up a string into a list of characters.                              *)

let char_explode (x:string) =
  let rec foo n cs =
     if (n < 0) then cs
                else let c = x.[n] in
                     foo (n-1) (c::cs) in
  foo (String.length x - 1) [];;


(* implode : string list -> string                                            *)
(*                                                                            *)
(* Joins a list of strings into a single string.                              *)

let implode xs =
  if (is_nonempty xs) then foldl1 (^) xs
                      else "";;


(* explode : string -> string list                                            *)
(*                                                                            *)
(* Breaks up a string into a list of single-character strings.                *)

let explode x =
  map (fun c -> String.make 1 c) (char_explode x);;


(* string_variant : string list -> string -> string                           *)
(*                                                                            *)
(* Creates a variant of the supplied string by appending apostrophes to its   *)
(* end until it avoids any string in the supplied avoidance list.  Does not   *)
(* append any apostrophes if the original string already avoids the avoidance *)
(* list.                                                                      *)

let rec string_variant xs0 x =
  if (mem x xs0)
    then string_variant xs0 (x ^ "'")
    else x;;


(* quote0 : string -> string                                                  *)
(*                                                                            *)
(* Puts single-quotes around the supplied string.  Does not perform any       *)
(* escaping of special characters.                                            *)

let quote0 x = "'" ^ x ^ "'";;


(* quote : string -> string                                                   *)
(*                                                                            *)
(* Puts double-quotes around the supplied string, backslash-escapes           *)
(* backslashes and double-quotes, and uses ASCII codes for backquotes and     *)
(* unprintable characters.                                                    *)

(* Note that it is not enough to entrust OCaml's 'String.escaped' to do the   *)
(* escaping, because exactly what gets escaped can be sensitive to the system *)
(* environment.  Also, 'String.escaped' does not escape backquotes, which are *)
(* used as delimeters for term/type quotations.                               *)

let char_escape c =
  let n = Char.code c in
  if (n = 34) || (n = 92)
    then char_implode ['\\'; c]
  else if (n >= 32) && (n <= 126) && not (n = 96)
    then char_implode [c]
    else let x = string_of_int n in
         match (String.length x) with
           1 -> "\\00" ^ x
         | 2 -> "\\0" ^ x
         | _ -> "\\" ^ x;;

let quote x =
  let x1 = (implode <* (map char_escape) <* char_explode) x in
  "\"" ^ x1 ^ "\"";;



(* ** REPORTING ** *)

(* This section is for functions that output messages to standard output.     *)


(* report : string -> unit                                                    *)
(*                                                                            *)
(* Outputs the supplied string prepended with "[HZ] " to standard output,     *)
(* followed by a full stop and newline, and then flushes the output stream.   *)

let report x =
  (print_string ("[HZ] " ^ x ^ ".\n");
   flush stdout);;


(* warn : string -> unit                                                      *)
(*                                                                            *)
(* Outputs the supplied string prepended with "[HZ] Warning - " to standard   *)
(* output, followed by a full stop and newline, and then flushes the output   *)
(* stream.                                                                    *)

let warn x = report ("WARNING: " ^ x);;



(* ** SORTING ** *)

(* This section is for functions that return lists sorted according to a      *)
(* given total order function.                                                *)


(* merge : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list                *)
(*                                                                            *)
(* Merges the two supplied sorted lists into a single sorted list, with       *)
(* respect to the supplied total order relation, assuming the supplied lists  *)
(* are already sorted with respect to the same relation.                      *)

let rec merge r xs ys =
  match (xs,ys) with
    (x0::xs0, y0::ys0) -> if (r x0 y0)
                            then x0::(merge r xs0 ys)
                            else y0::(merge r xs ys0)
  | (      _, []     ) -> xs
  | (     [], _      ) -> ys;;


(* mergesort : ('a -> 'a -> bool) -> 'a list -> 'a list                       *)
(*                                                                            *)
(* Sorts the supplied list using the merge technique, with respect to the     *)
(* supplied total order relation.                                             *)

let mergesort r xs =
  let rec mergepairs yss xss =
     match (yss,xss) with
       ([ys], [])             -> ys
     | (   _, [])             -> mergepairs [] (rev yss)
     | (   _, [xs0])          -> mergepairs (xs0::yss) []
     | (   _, xs1::xs2::xss3) -> mergepairs ((merge r xs1 xs2)::yss) xss3 in
  if (is_empty xs)
    then xs
    else mergepairs [] (map (fun x -> [x]) xs);;


end;;
