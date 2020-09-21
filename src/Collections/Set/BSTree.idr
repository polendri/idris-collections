module Collections.Set.BSTree

import Collections.Set
import Collections.Map.BSTree as M
import Collections.Map.BSTree.Core as MC
import Collections.Util.Bnd
import Decidable.Order.Strict

||| A verified binary search tree with erased proofs.
|||
||| The values in the tree are constrained by min/max bounds, which make use of `Bnd` to extend the
||| tree value type with `Top` and `Bot` values. This allows for a natural way to leave bounds
||| unconstrained (by having a minimum of `Bot` or a maximum of `Top`).
|||
||| @ sto The strict total ordering used in the tree. Since a `StrictOrdered` impl is w.r.t. a type
|||       `a`, the type of tree values is defined implicitly by `sto`.
||| @ min The minimum value constraint, proving that `sto min (Mid x)` for all values `x` in the tree.
||| @ max The maximum value constraint, proving that `sto (Mid x) max` for all values `x` in the tree.
public export
BST : {0 a : Type} ->
      {0 to : a -> a -> Type} ->
      (sto : StrictOrdered a to) ->
      (min,max : Bnd a) ->
      Type
BST sto min max = MC.BST sto () min max

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
BSTree sto = BST sto () Bot Top

export
empty : (sto : StrictOrdered a to) => BSTree sto ()
empty = M.empty

export
singleton : (sto : StrictOrdered a to) =>
            (x : a) ->
            BSTree sto
singleton x = M.singleton x ()

export
insert : (sto : StrictOrdered a to) =>
         (x : a) ->
         BSTree sto ->
         BSTree sto
insert x t = M.insert x () t

export
(sto : StrictOrdered a to) => Set a (BSTree sto) where
  empty = M.empty
  singleton x = M.singleton x ()
  insert x t = M.insert x () t
