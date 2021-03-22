module Collections.BSTree.Set.Core

import Collections.Util.Bnd
import Collections.BSTree.Map.Core as M
import Decidable.Order.Strict

||| A verified binary search tree with erased proofs.
|||
||| The keys in the tree are constrained by min/max bounds, which make use of `Bnd` to extend the
||| tree key type with `Top` and `Bot` values. This allows for a natural way to leave bounds
||| unconstrained (by having a minimum of `Bot` or a maximum of `Top`).
|||
||| @ ord The ordering implementations used in the tree. Since these are w.r.t. a type `kTy`, the
|||       type of tree keys is defined implicitly by `ord`.
||| @ min The minimum value constraint, proving that `sto min (Mid x)` for all values `x` in the
|||       tree.
||| @ max The maximum value constraint, proving that `sto (Mid x) max` for all values `x` in the
|||       tree.
public export
BST : {0 sto : kTy -> kTy -> Type} ->
      (pre : StrictPreorder kTy sto) ->
      (tot : StrictOrdered kTy sto) ->
      (0 min,max : Bnd kTy) ->
      Type
BST pre tot min max = M.BST pre tot () min max
%name Collections.BSTree.Set.Core.BST t,u,v

||| A verified binary search tree with erased proofs.
|||
||| This is an alias for the more generic `BST` (which accepts min/max bounds for its contents).
||| The bounds are necessary for verifying the structure of a tree, but the root node of any
||| `BST` will always be unconstrained. So generally, `BST` can be considered an implementation
||| detail.
|||
||| @ ord The strict total ordering used in the tree. Since a `StrictOrdered` impl is w.r.t. a type
|||       `kTy`, the type of tree values is defined implicitly by `ord`.
public export
BSTree : {0 kTy : Type} ->
         (0 sto : kTy -> kTy -> Type) ->
         {auto pre : StrictPreorder kTy sto} ->
         {auto tot : StrictOrdered kTy sto} ->
         Type
BSTree sto {pre} {tot} = M.BST pre tot () Bot Top
%name Collections.BSTree.Set.Core.BSTree t,u,v
