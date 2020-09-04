module Collections.Set.BSTree.Core

import Collections.Util.Bnd
import Data.DPair
import Data.Nat
import Decidable.Equality
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
data BST : {0 a : Type} ->
           {0 to : a -> a -> Type} ->
           (0 sto : StrictOrdered a to) ->
           (0 min,max : Bnd a) ->
           Type where
  Empty : {0 sto : StrictOrdered a to} ->
          {0 min,max : Bnd a} ->
          (0 prf : BndLT to min max) ->
          BST sto min max
  Node  : {0 sto : StrictOrdered a to} ->
          {0 min,max : Bnd a} ->
          (x : a) ->
          (l : BST sto min (Mid x)) ->
          (r : BST sto (Mid x) max) ->
          BST sto min max
%name BST t,u,v
