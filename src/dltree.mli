(* ========================================================================== *)
(* DYNAMIC LOOKUP TREES (HOL Zero)                                            *)
(* - Library support for data storage in dynamic indexed binary trees         *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2014                            *)
(* ========================================================================== *)


module type DLTree_sig = sig

  type ('a,'b) dltree =
         Node of int * ('a * 'b) * ('a,'b) dltree * ('a,'b) dltree
       | Leaf
  val dltree_empty : ('a,'b) dltree
  val dltree_make : ('a * 'b) list -> ('a,'b) dltree
  val dltree_mem : 'a -> ('a,'b) dltree -> bool
  val dltree_lookup : 'a -> ('a,'b) dltree -> 'b
  val dltree_replace : 'a * 'b -> ('a,'b) dltree -> ('a,'b) dltree
  val dltree_elem : 'a -> ('a,'b) dltree -> 'a * 'b
  val dltree_elems : ('a,'b) dltree -> ('a * 'b) list
  val dltree_insert : 'a * 'b -> ('a,'b) dltree -> ('a,'b) dltree
  val dltree_delete : 'a -> ('a,'b) dltree -> ('a,'b) dltree

end;;
