module Collections.BSTree.Map.Core

import Collections.Util.Bnd
import Decidable.Order.Strict

||| A verified binary search tree with erased proofs.
|||
||| The keys in the tree are constrained by min/max bounds, which make use of `Bnd` to extend the
||| tree key type with `Top` and `Bot` values. This allows for a natural way to leave bounds
||| unconstrained (by having a minimum of `Bot` or a maximum of `Top`).
|||
||| @ ord The ordering implementations used in the tree. Since these are w.r.t. a type `kTy`, the
|||       type of tree keys is defined implicitly by `ord`.
||| @ vTy The data type to carry in nodes in addition to the key type `kTy`.
||| @ min The minimum value constraint, proving that `sto min (Mid x)` for all values `x` in the
|||       tree.
||| @ max The maximum value constraint, proving that `sto (Mid x) max` for all values `x` in the
|||       tree.
public export
data BST : {0 sto : kTy -> kTy -> Type} ->
           (pre : StrictPreorder kTy sto) ->
           (tot : StrictOrdered kTy sto) ->
           (0 vTy : Type) ->
           (0 min,max : Bnd kTy) ->
           Type where
  ||| An empty tree node.
  |||
  ||| @ prf An ordering proof on the min and max constraints of this node. Since an in-order
  |||       traversal of a binary tree is an empty-node-empty-... alternation, storing ordering
  |||       information in the empty nodes is a natural way to store evidence that the nodes are in
  |||       order.
  Empty : {pre : StrictPreorder kTy sto} ->
          {tot : StrictOrdered kTy sto} ->
          (0 prf : BndLT sto min max) ->
          BST pre tot vTy min max
  ||| A node with a value and with left and right subtrees, each with appropriate bounds relative
  ||| to the key `k` of the node.
  |||
  ||| @ l The left subtree invariant
  ||| @ r The right subtree invariant
  Node  : {0 sto : kTy -> kTy -> Type} ->
          {pre : StrictPreorder kTy sto} ->
          {tot : StrictOrdered kTy sto} ->
          (k : kTy) ->
          (v : vTy) ->
          (l : BST pre tot vTy min (Mid k)) ->
          (r : BST pre tot vTy (Mid k) max) ->
          BST pre tot vTy min max
%name BST t,u,v

||| A verified binary search tree with erased proofs.
|||
||| This is an alias for the more generic `BST` (which accepts min/max bounds for its contents).
||| The bounds are necessary for verifying the structure of a tree, but the root node of any
||| `BST` will always be unconstrained. So generally, `BST` can be considered an implementation
||| detail.
|||
||| @ ord The strict total ordering used in the tree. Since a `StrictOrdered` impl is w.r.t. a type
|||       `kTy`, the type of tree values is defined implicitly by `ord`.
||| @ vTy The type for values stored in nodes of the tree.
public export
BSTree : {0 kTy : Type} ->
         (0 sto : kTy -> kTy -> Type) ->
         {auto pre : StrictPreorder kTy sto} ->
         {auto tot : StrictOrdered kTy sto} ->
         (0 vTy : Type) ->
         Type
BSTree sto {pre} {tot} vTy = BST pre tot vTy Bot Top
%name BSTree t,u,v

||| Proof that the minimum bound can be decreased arbitrarily.
public export
extendMin : {0 sto : kTy -> kTy -> Type} ->
            {pre : StrictPreorder kTy sto} ->
            {tot : StrictOrdered kTy sto} ->
            (0 prf : BndLT sto min' min) ->
            BST pre tot vTy min max ->
            BST pre tot vTy min' max
extendMin {pre} prf (Empty prf')   = Empty $ transitive min' min max prf prf'
extendMin       prf (Node k v l r) = Node k v (extendMin prf l) r

||| Proof that the maximum bound can be increased arbitrarily.
public export
extendMax : {0 sto : kTy -> kTy -> Type} ->
            {pre : StrictPreorder kTy sto} ->
            {tot : StrictOrdered kTy sto} ->
            (0 prf : BndLT sto max max') ->
            BST pre tot vTy min max ->
            BST pre tot vTy min max'
extendMax {pre} prf (Empty prf')   = Empty $ transitive min max max' prf' prf
extendMax       prf (Node k v l r) = Node k v l (extendMax prf r)
