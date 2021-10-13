module Collections.BSTree.Map.Core

import Collections.Util.Bnd
import Control.Relation
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
||| @ mn  The minimum value constraint, proving that `rel mn (Mid x)` for all values `x` in the
|||       tree.
||| @ mx  The maximum value constraint, proving that `rel (Mid x) mx` for all values `x` in the
|||       tree.
public export
data BST : {0 rel : kTy -> kTy -> Type} ->
           (pre : StrictPreorder kTy rel) ->
           (tot : StrictOrdered kTy rel) ->
           (0 vTy : Type) ->
           (0 mn,mx : Bnd kTy) ->
           Type where
  ||| An empty tree node.
  |||
  ||| @ prf An ordering proof on the min and max constraints of this node. Since an in-order
  |||       traversal of a binary tree is an empty-node-empty-... alternation, storing ordering
  |||       information in the empty nodes is a natural way to store evidence that the nodes are in
  |||       order.
  Empty : {pre : StrictPreorder kTy rel} ->
          {tot : StrictOrdered kTy rel} ->
          (0 prf : BndLT rel mn mx) ->
          BST pre tot vTy mn mx
  ||| A node with a value and with left and right subtrees, each with appropriate bounds relative
  ||| to the key `k` of the node.
  |||
  ||| @ k The key value of the node
  ||| @ v The data value of the node
  ||| @ l The left subtree
  ||| @ r The right subtree
  Node  : {0 rel : kTy -> kTy -> Type} ->
          {pre : StrictPreorder kTy rel} ->
          {tot : StrictOrdered kTy rel} ->
          (k : kTy) ->
          (v : vTy) ->
          (l : BST pre tot vTy mn (Mid k)) ->
          (r : BST pre tot vTy (Mid k) mx) ->
          BST pre tot vTy mn mx
%name BST t,u,v

||| A verified binary search tree with erased proofs.
|||
||| This is an alias for the more generic `BST` (which accepts min/max bounds for its contents).
||| The bounds are necessary for verifying the structure of a tree, but the root node of any
||| `BST` will always be unconstrained. So generally, `BST` can be considered an implementation
||| detail.
|||
||| @ rel The strict total ordering used in the tree. Since a `StrictOrdered` impl is w.r.t. a type
|||       `kTy`, the type of tree values is defined implicitly by `ord`.
||| @ vTy The type for values stored in nodes of the tree.
public export
BSTree : {0 kTy : Type} ->
         (0 rel : kTy -> kTy -> Type) ->
         {auto pre : StrictPreorder kTy rel} ->
         {auto tot : StrictOrdered kTy rel} ->
         (0 vTy : Type) ->
         Type
BSTree rel {pre} {tot} vTy = BST pre tot vTy Bot Top
%name BSTree t,u,v

||| Proof that the minimum bound can be decreased arbitrarily.
public export
extendMin : {0 rel : kTy -> kTy -> Type} ->
            {pre : StrictPreorder kTy rel} ->
            {tot : StrictOrdered kTy rel} ->
            (0 prf : BndLT rel mn' mn) ->
            BST pre tot vTy mn mx ->
            BST pre tot vTy mn' mx
extendMin {pre} prf (Empty prf')   = Empty $ transitive {x=mn'} {y=mn} {z=mx} prf prf'
extendMin       prf (Node k v l r) = Node k v (extendMin prf l) r

||| Proof that the maximum bound can be increased arbitrarily.
public export
extendMax : {0 rel : kTy -> kTy -> Type} ->
            {pre : StrictPreorder kTy rel} ->
            {tot : StrictOrdered kTy rel} ->
            (0 prf : BndLT rel mx mx') ->
            BST pre tot vTy mn mx ->
            BST pre tot vTy mn mx'
extendMax {pre} prf (Empty prf')   = Empty $ transitive {x=mn} {y=mx} {z=mx'} prf' prf
extendMax       prf (Node k v l r) = Node k v l (extendMax prf r)
