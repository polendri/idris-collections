module Collections.Map.BSTree.Core

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
|||       `kTy`, the type of tree values is defined implicitly by `sto`.
||| @ vTy The "data" type to carry in nodes in addition to the ordered type `kTy`.
||| @ min The minimum value constraint, proving that `sto min (Mid x)` for all values `x` in the tree.
||| @ max The maximum value constraint, proving that `sto (Mid x) max` for all values `x` in the tree.
public export
data BST : {0 kTy : Type} ->
           {0 to : kTy -> kTy -> Type} ->
           (0 sto : StrictOrdered kTy to) ->
           (0 vTy : Type) ->
           (0 min,max : Bnd kTy) ->
           Type where
  ||| An empty tree node.
  |||
  ||| @ prf An ordering proof on the min and max constraints of this node. Since an in-order
  |||       traversal of a binary tree is an empty-node-empty-... alternation, storing ordering
  |||       information in the empty nodes is a natural way to store evidence that the nodes are in
  |||       order.
  Empty : {0 sto : StrictOrdered kTy to} ->
          {0 min,max : Bnd kTy} ->
          (0 prf : BndLT to min max) ->
          BST sto vTy min max
  ||| A node with a value and with left and right subtrees.
  Node  : {0 sto : StrictOrdered kTy to} ->
          (k : kTy) ->
          (v : vTy) ->
          (l : BST sto vTy min (Mid k)) ->
          (r : BST sto vTy (Mid k) max) ->
          BST sto vTy min max
%name BST t,u,v
