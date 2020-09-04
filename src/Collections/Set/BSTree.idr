module Collections.Set.BSTree

import Collections.Set
import Collections.Util.Bnd
import Decidable.Order.Strict

import public Collections.Set.BSTree.Core

||| A verified binary search tree with erased proofs.
|||
||| This is an alias for the more generic `BST`, which accepts min/max bounds for its contents.
||| The bounds are necessary for verifying the structure of a tree, but the root node of any
||| `BST` will always be unconstrained. So generally, `BST` can be used when working with trees,
||| with `BST` left as an implementation detail.
|||
||| @ sto The strict total ordering used in the tree. Since a `StrictOrdered` impl is w.r.t. a type
|||       `a`, the type of tree values is defined implicitly by `sto`.
public export
BSTree : (sto : StrictOrdered a to) -> Type
BSTree sto = BST sto Bot Top

export
empty : (sto : StrictOrdered a to) => BST sto Bot Top
empty = Empty BotLTTop

export
singleton : (sto : StrictOrdered a to) =>
            (x : a) ->
            BST sto Bot Top
singleton x = Node x (Empty BotLTMid) (Empty MidLTTop)

export
insert' : (sto : StrictOrdered a to) =>
          {0 min,max : Bnd a} ->
          (x : a) ->
          (BndLT to min (Mid x), BndLT to (Mid x) max) ->
          BST sto min max ->
          BST sto min max
insert' x (lx, xu) (Empty _) = Node x (Empty lx) (Empty xu)
insert' x (lx, xu) (Node y l r) =
  case order {spo=BndLT to} (Mid x) (Mid y) of
       DecLT xy   => Node y (insert' x (lx, xy) l) r
       DecEQ Refl => Node x l r
       DecGT yx   => Node y l (insert' x (yx, xu) r)

insert : (sto : StrictOrdered a to) =>
         (x : a) ->
         BSTree sto ->
         BSTree sto
insert x t = insert' x (BotLTMid, MidLTTop) t

(sto : StrictOrdered a to) => Set a (BSTree sto) where
  empty = empty
  singleton x = singleton x
  insert x t = insert x t
