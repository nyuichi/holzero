(* ========================================================================== *)
(* DYNAMIC LOOKUP TREES (HOL Zero)                                            *)
(* - Library support for data storage in dynamic indexed binary trees         *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2014                            *)
(* ========================================================================== *)


module DLTree : DLTree_sig = struct


(* This module provides library support for dynamic lookup trees.  These are  *)
(* lookup tables implemented as self-balancing binary search trees that store *)
(* information on nodes ordered according to indexes.  Indexes are ordered    *)
(* under OCaml's '<' operator.  Multiple entries under the same index are not *)
(* allowed.                                                                   *)

(* This is implemented as AA trees (also called Andersson trees), that stay   *)
(* balanced within a factor of 2 - i.e. the maximum distance from root to     *)
(* leaf is no more than twice the minimum distance.  This has a fairly simple *)
(* implementation and yet is one of the most efficient forms of self-         *)
(* balancing tree, with lookup, insertion and deletion all having worst case  *)
(* O(log n) time and space complexity.                                        *)


(* AA trees *)

(* AA trees are a variation of classic binary search trees that maintain an   *)
(* additional invariant property, called the "AA invariant", for ensuring     *)
(* that the tree stays balanced within a factor of 2.  This invariant uses    *)
(* the concept of "level" - an integer-valued measure of the depth of a given *)
(* tree or subtree.                                                           *)

(* The AA invariant has four aspects:                                         *)
(*  1. Every leaf's level is 0;                                               *)
(*  2. Every node's left branch level is one less than its parent's;          *)
(*  3. Every node's right branch level is equal to or one less than its       *)
(*    parent's;                                                               *)
(*  4. Every node's right-right branch level is less than its grandparent's.  *)

(* Thus the level represents the distance from the node to the left-most leaf *)
(* descendant of the node, and an upper bound of half the distance from the   *)
(* node to its right-most leaf descendant.  Thus the level is an upper bound  *)
(* for half the tree depth, and is also an upper bound for the difference     *)
(* between the depths of the deepest and least deep leaves.                   *)

(* Insertion and deletion of tree entries preserve the AA invariant by        *)
(* employing a combination of two rebalancing operations ("skew" and "split") *)
(* and a level adjustment operation ("decrease-level") after the basic        *)
(* insertion/deletion.  These three operations all have time/space-complexity *)
(* O(1), and the number of nodes that they need to operate on per operation   *)
(* is at most O(log n), thus ensuring that both insertion and deletion have   *)
(* O(log n) time/space-complexity.  The particular combination of skews,      *)
(* splits and decrease-levels employed depends on whether an insertion or     *)
(* deletion is being performed.                                               *)

(* Note that to ensure correct functionality (i.e. that entries can be looked *)
(* up according to the insertions and deletions that have taken place), it is *)
(* sufficient that the insertion and deletion operations preserve classic     *)
(* binary search tree correct ordering wrt '<'.  That is, the AA invariant is *)
(* purely for efficiency, rather than correctness.  Note also that the three  *)
(* adjustment operations all preserve correct ordering.                       *)


(* dltree datatype *)

(* The 'dltree' datatype is a binary lookup tree datatype, where an index and *)
(* item are held at each node, and leaves hold no information.  Comparison    *)
(* between indexes is done using the polymorphic '<' total order relation.    *)
(* Each node also holds an integer for its AA level, to enable the AA         *)
(* invariant to be maintained.  Note that there is no need for leaves to hold *)
(* their level, because it is always 0.                                       *)

type ('a,'b) dltree =
   Node of int * ('a * 'b) * ('a,'b) dltree * ('a,'b) dltree
 | Leaf;;


(* dltree_empty : ('a,'b) dltree                                              *)
(*                                                                            *)
(* Returns a fresh empty dltree.                                              *)

let dltree_empty = Leaf;;


(* dltree_load : elem list -> dltree                                          *)
(*                                                                            *)
(* Creates a filled lookup tree from an unsorted list of index-value pairs.   *)

let rec log2_0 l n =
  if (n < 2)
    then l
    else log2_0 (l+1) (n/2);;

let log2 n = log2_0 0 n;;

let rec dltree_unchecked_load0 n xys =
  if (n >= 0)
    then let i = n / 2 in
         let (xys1,xys02) = cut i xys in 
         let (xy,xys2) = hd_tl xys02 in
         let h = log2 (n+2) in
         let tr1 = dltree_unchecked_load0 (i-1) xys1 in
         let tr2 = dltree_unchecked_load0 (n-i-1) xys2 in
         Node (h,xy,tr1,tr2)
    else Leaf;;

let dltree_unchecked_load xys =
  dltree_unchecked_load0 (length xys - 1) xys;;

let dltree_make xys =
  let lt (x1,y1) (x2,y2) = (x1 < x2) in
  let xys' =mergesort lt xys in
  dltree_unchecked_load xys';;


(* dltree_elems : ('a,'b) dltree -> ('a * 'b) list                            *)
(*                                                                            *)
(* Converts the information held in a given lookup tree into an index-ordered *)
(* association list.                                                          *)

let rec dltree_elems0 tr xys0 =
  match tr with
    Node (_,xy,tr1,tr2) -> dltree_elems0 tr1 (xy::(dltree_elems0 tr2 xys0))
  | Leaf                -> xys0;;

let dltree_elems tr = dltree_elems0 tr [];;


(* Basic subtree operations *)

let level tr =
  match tr with
    Node (h,_,_,_) -> h
  | Leaf           -> 0;;

let rec rightmost_elem xy0 tr =
  match tr with
    Node (_,xy,_,tr2) -> rightmost_elem xy tr2
  | Leaf              -> xy0;;

let right_app f tr =
  match tr with
    Node (h,xy,tr1,tr2)
       -> Node (h, xy, tr1, f tr2)
  | _  -> tr;;


(* decrease_level *)

(* This operation reduces the level of a node if the difference between its   *)
(* current level and the level of its subnodes is greater than 1.             *)

let decrease_level0 h0 tr =
  match tr with
    Node (h,xy,tr1,tr2) when (h > h0)
       -> Node (h0,xy,tr1,tr2)
  | _  -> tr;;

let decrease_level tr =
  match tr with
    Node (h,_,tr1,tr2)
       -> let h0 = min (level tr1) (level tr2) + 1 in
          if (h > h0)
            then (right_app (decrease_level0 h0) <* decrease_level0 h0) tr
            else tr
  | _  -> tr;;


(* skew *)

(* The skew operation performs a single right rotation to rebalance when the  *)
(* left child has the same level as its parent.                               *)
(*                                                                            *)
(*           D[n]                     B[n]                                    *)
(*          /    \                   /    \                                   *)
(*        B[n]  E[..]     -->     A[..]  D[n]                                 *)
(*       /   \                           /   \                                *)
(*    A[..]  C[..]                    C[..]  E[..]                            *)

let skew tr =
  match tr with
    Node (h, xy, Node (h1,xy1,tr11,tr12), tr2) when (h1 = h)
       -> Node (h1, xy1, tr11, Node (h,xy,tr12,tr2))
  | _  -> tr;;


(* split *)

(* The split operation performs a single left rotation to rebalance when the  *)
(* right-right grandchild has the same level as its grandparent, incrementing *)
(* the level of the resulting top-level node.                                 *)
(*                                                                            *)
(*        B[n]                      D[n+1]                                    *)
(*       /    \                     /    \                                    *)
(*    A[..]  D[n]      -->        B[n]  E[n]                                  *)
(*           /  \                /   \                                        *)
(*       C[..]  E[n]          A[..]  C[..]                                    *)

let split tr =
  match tr with
    Node (h, xy, tr1, Node (h2,xy2,tr21,tr22)) when (level tr22 = h)
       -> Node (h2 + 1, xy2, Node (h,xy,tr1,tr21), tr22)
  | _  -> tr;;


(* dltree_insert : 'a * 'b -> ('a,'b) dltree -> ('a,'b) dltree                *)
(*                                                                            *)
(* Inserts the supplied single indexed item into a given lookup tree.  Fails  *)
(* if the tree already contains an entry for the supplied index.              *)

(* The tree potentially needs to be rebalanced at each node from the          *)
(* insertion point up to the root, and this can be done by a skew followed by *)
(* a split.                                                                   *)

let rec dltree_insert ((x0,_) as xy0) tr =
  let rebalance = (split <* skew) in
  match tr with
    Node (h,((x,_) as xy),tr1,tr2)
       -> if (x0 < x)
            then (* Put into left branch     *)
                 rebalance (Node (h, xy, dltree_insert xy0 tr1, tr2))
          else if (x < x0)
            then (* Put into right branch    *)
                 rebalance (Node (h, xy, tr1, dltree_insert xy0 tr2))
            else (* Element already in tree  *)
                 hol_fail ("dltree_insert","Already in tree")
  | Leaf
       -> (* Put element here *)
          Node (1, xy0, Leaf, Leaf);;


(* dltree_delete : 'a -> ('a,'b) dltree -> ('a,'b) dltree                     *)
(*                                                                            *)
(* Deletes the entry at the supplied index in a given lookup tree.  Fails if  *)
(* the tree does not contain an entry for the supplied index.                 *)

(* The tree potentially needs to be rebalanced at each node from the deletion *)
(* point up to the root, and this can be done by adjusting the level of the   *)
(* node, followed by a series of skews and then splits.                       *)

let rec dltree_delete x0 tr =
  let rebalance = (right_app split <* split <*
                   right_app (right_app skew) <* right_app skew <* skew <*
                   decrease_level) in
  match tr with
    Node (h,((x,_) as xy),tr1,tr2)
       -> if (x0 < x)
            then (* Element should be in left branch *)
                 rebalance (Node (h, xy, dltree_delete x0 tr1, tr2))
          else if (x < x0)
            then (* Element should be in right branch *)
                 rebalance (Node (h, xy, tr1, dltree_delete x0 tr2))
            else (* Node holds element to be deleted *)
                 (match (tr1,tr2) with
                    (Leaf,_) -> tr2
                  | (_,Leaf) -> tr1
                  | _  -> let (x1,_) as xy1 = rightmost_elem xy tr1 in
                          rebalance (Node (h, xy1, dltree_delete x1 tr1, tr2)))
  | Leaf
       -> (* Element not in tree *)
          hol_fail ("dltree_delete","Not in tree");;


(* dltree_elem : 'a -> ('a,'b) dltree -> 'a * 'b                              *)
(*                                                                            *)
(* Returns the index and item held at the supplied index in a given lookup    *)
(* tree.  Fails if the tree has no entry for the supplied index.              *)

let rec dltree_elem x0 tr =
  match tr with
    Node (_, ((x,_) as xy), tr1, tr2)
         -> if (x0 < x)
              then dltree_elem x0 tr1
            else if (x < x0)
              then dltree_elem x0 tr2
              else xy
  | Leaf -> hol_fail ("dltree_elem","Not in tree");;


(* dltree_lookup : 'a -> ('a,'b) dltree -> 'b                                 *)
(*                                                                            *)
(* Returns the item held at the supplied index in a given lookup tree.        *)

let rec dltree_lookup x0 tr =
  let (_,y) = try2 (dltree_elem x0) tr      "dltree_lookup" in
  y;;


(* dltree_replace : 'a * 'b -> ('a,'b) dltree -> ('a,'b) dltree               *)
(*                                                                            *)
(* Replaces in a given AA tree the existing entry that is equivalent to the   *)
(* supplied element, replacing it with the supplied element itself.           *)

let rec dltree_replace ((x0,_) as xy0) tr =
  match tr with
    Node (h,((x,_) as xy),tr1,tr2)
       -> if (x0 < x)
            then (* Put into left branch     *)
                 Node (h, xy, dltree_replace xy0 tr1, tr2)
          else if (x < x0)
            then (* Put into right branch    *)
                 Node (h, xy, tr1, dltree_replace xy0 tr2)
            else (* Replace existing entry   *)
                 Node (h, xy0, tr1, tr2)
  | Leaf
       -> (* Error case *)
          hol_fail ("dltree_replace","Not in tree");;


(* dltree_mem : 'a -> ('a,'b) dltree -> bool                                  *)
(*                                                                            *)
(* Returns "true" iff the supplied index occurs in a given lookup tree.       *)

let rec dltree_mem x0 tr =
  match tr with
    Node (_,(x,_),tr1,tr2)
         -> if (x0 < x)
              then dltree_mem x0 tr1
            else if (x < x0)
              then dltree_mem x0 tr2
              else true
  | Leaf -> false;;


end;;
