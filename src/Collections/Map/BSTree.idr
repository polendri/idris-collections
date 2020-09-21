module Collections.Map.BSTree

import Collections.Map
import Collections.Util.Bnd
import Decidable.Order.Strict

import public Collections.Map.BSTree.Core

||| A verified binary search tree with erased proofs.
|||
||| This is an alias for the more generic `BST`, which accepts min/max bounds for its contents.
||| The bounds are necessary for verifying the structure of a tree, but the root node of any
||| `BST` will always be unconstrained. So generally, `BST` can be used when working with trees,
||| with `BST` left as an implementation detail.
|||
||| @ sto The strict total ordering used in the tree. Since a `StrictOrdered` impl is w.r.t. a type
|||       `a`, the type of tree values is defined implicitly by `sto`.
||| @ vTy The type of values stored in nodes of the tree.
public export
BSTree : (sto : StrictOrdered kTy to) -> (vTy : Type) -> Type
BSTree sto vTy = BST sto vTy Bot Top

export
empty : (sto : StrictOrdered a to) => BSTree sto vTy
empty = Empty BotLTTop

export
singleton : (sto : StrictOrdered kTy to) =>
            (k : kTy) ->
            (v : vTy) ->
            BSTree sto vTy
singleton k v = Node k v (Empty BotLTMid) (Empty MidLTTop)

insert' : (sto : StrictOrdered kTy to) =>
          {0 min,max : Bnd kTy} ->
          (k : kTy) ->
          (v : vTy) ->
          (BndLT to min (Mid k), BndLT to (Mid k) max) ->
          BST sto vTy min max ->
          BST sto vTy min max
insert' x vX (lx, xu) (Empty _) = Node x vX (Empty lx) (Empty xu)
insert' x vX (lx, xu) (Node y vY l r) =
  case order {spo=BndLT to} (Mid x) (Mid y) of
       DecLT xy   => Node y vY (insert' x vX (lx, xy) l) r
       DecEQ Refl => Node x vX l r
       DecGT yx   => Node y vY l (insert' x vX (yx, xu) r)

export
insert : (sto : StrictOrdered kTy to) =>
         (k : kTy) ->
         (v : vTy) ->
         BSTree sto vTy ->
         BSTree sto vTy
insert k v t = insert' k v (BotLTMid, MidLTTop) t

export
(sto : StrictOrdered kTy to) => Map kTy vTy (BSTree sto vTy) where
  empty = empty
  singleton k v = singleton k v
  insert k v t = insert k v t
