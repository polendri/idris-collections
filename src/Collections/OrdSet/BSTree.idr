module Collections.OrdSet.BSTree

import Collections.OrdSet
import Collections.OrdMap.BSTree as M
import Collections.OrdMap.BSTree.Core as MC
import Collections.Util.Bnd
import Decidable.Order.Strict

||| A verified binary search tree with erased proofs.
|||
||| The values in the tree are constrained by min/max bounds, which make use of `Bnd` to extend the
||| tree value type with `Top` and `Bot` values. This allows for a natural way to leave bounds
||| unconstrained (by having a minimum of `Bot` or a maximum of `Top`).
|||
||| @ ord The strict total ordering used in the tree. Since a `StrictOrdered` impl is w.r.t. a type
|||       `a`, the type of tree values is defined implicitly by `ord`.
||| @ min The minimum value constraint, proving that `sto min (Mid x)` for all values `x` in the tree.
||| @ max The maximum value constraint, proving that `sto (Mid x) max` for all values `x` in the tree.
public export
BST : {0 a : Type} ->
      {0 sto : a -> a -> Type} ->
      (ord : StrictOrdered a sto) ->
      (0 min,max : Bnd a) ->
      Type
BST ord min max = MC.BST ord () min max

||| A verified binary search tree with erased proofs.
|||
||| This is an alias for the more generic `BST`, which accepts min/max bounds for its contents.
||| The bounds are necessary for verifying the structure of a tree, but the root node of any
||| `BST` will always be unconstrained. So generally, `BST` can be used when working with trees,
||| with `BST` left as an implementation detail.
|||
||| @ ord The strict total ordering used in the tree. Since a `StrictOrdered` impl is w.r.t. a type
|||       `a`, the type of tree values is defined implicitly by `ord`.
public export
BSTree : {0 a : Type} ->
         {0 sto : a -> a -> Type} ->
         (ord : StrictOrdered a sto) ->
         Type
BSTree ord = BST ord () Bot Top

export
empty : (sto : StrictOrdered a to) => BSTree sto ()
empty = M.BSTree.empty

export
insert : (sto : StrictOrdered a to) =>
         (x : a) ->
         BSTree sto ->
         BSTree sto
insert x t = M.BSTree.insert x () t

-- export
-- (sto : StrictOrdered a to) => Set a (BSTree sto) where
--   empty = M.BSTree.empty
--   insert x t = M.BSTree.insert x () t
