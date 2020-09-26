module Collections.OrdMap.BSTree.Core

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
||| @ ord The strict total ordering used in the tree. Since a `StrictOrdered` impl is w.r.t. a type
|||       `kTy`, the type of tree values is defined implicitly by `ord`.
||| @ vTy The "data" type to carry in nodes in addition to the ordered type `kTy`.
||| @ min The minimum value constraint, proving that `sto min (Mid x)` for all values `x` in the tree.
||| @ max The maximum value constraint, proving that `sto (Mid x) max` for all values `x` in the tree.
public export
data BST : {0 kTy : Type} ->
           {0 sto : kTy -> kTy -> Type} ->
           (ord : StrictOrdered kTy sto) ->
           (0 vTy : Type) ->
           (0 min,max : Bnd kTy) ->
           Type where
  ||| An empty tree node.
  |||
  ||| @ prf An ordering proof on the min and max constraints of this node. Since an in-order
  |||       traversal of a binary tree is an empty-node-empty-... alternation, storing ordering
  |||       information in the empty nodes is a natural way to store evidence that the nodes are in
  |||       order.
  Empty : {ord : StrictOrdered kTy sto} ->
          {0 min,max : Bnd kTy} ->
          (0 prf : BndLT sto min max) ->
          BST ord vTy min max
  ||| A node with a value and with left and right subtrees.
  Node  : {ord : StrictOrdered kTy sto} ->
          (k : kTy) ->
          (v : vTy) ->
          (l : BST ord vTy min (Mid k)) ->
          (r : BST ord vTy (Mid k) max) ->
          BST ord vTy min max
%name BST t,u,v

||| A verified binary search tree with erased proofs.
|||
||| This is an alias for the more generic `BST`, which accepts min/max bounds for its contents.
||| The bounds are necessary for verifying the structure of a tree, but the root node of any
||| `BST` will always be unconstrained. So generally, `BST` can be used when working with trees,
||| with `BST` left as an implementation detail.
|||
||| @ kTy The type for keys stored in nodes of the tree.
||| @ ord The strict total ordering used in the tree. Since a `StrictOrdered` impl is w.r.t. a type
|||       `a`, the type of tree values is defined implicitly by `ord`.
||| @ vTy The type for values stored in nodes of the tree.
public export
BSTree : {0 kTy : Type} ->
         {0 sto : kTy -> kTy -> Type} ->
         (ord : StrictOrdered kTy sto) ->
         (0 vTy : Type) ->
         Type
BSTree ord vTy = BST ord vTy Bot Top

||| Proof that the minimum bound can be decreased arbitrarily.
export
extendMin : {ord : StrictOrdered kTy sto} ->
            (0 prf : BndLT sto min' min) ->
            BST ord vTy min max ->
            BST ord vTy min' max
extendMin prf (Empty prf') = Empty $ transitive min' min max prf prf'
extendMin prf (Node k v l r) = Node k v (extendMin prf l) r

||| Proof that the maximum bound can be increased arbitrarily.
export
extendMax : {ord : StrictOrdered kTy sto} ->
            (0 prf : BndLT sto max max') ->
            BST ord vTy min max ->
            BST ord vTy min max'
extendMax prf (Empty prf') = Empty $ transitive min max max' prf' prf
extendMax prf (Node k v l r) = Node k v l (extendMax prf r)
