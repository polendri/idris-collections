module Collections.Map.BSTree.Elem

import Collections.Map.BSTree
import Collections.Util.Bnd
import Decidable.Order.Strict

namespace Key
  ||| Proof that a key is contained in a `BSTree`.
  |||
  ||| @ k The key whose presence is being asserted
  ||| @ t The tree in which `k` is present
  public export
  data Elem : {0 sto : StrictOrdered kTy to} ->
              (0 k : kTy) ->
              (0 t : BST sto vTy min max) ->
              Type where
    ||| Proof that `k` is at the root of the tree.
    Here    : Elem k (Node k v l r)
    ||| Proof that `k` is in the left subtree.
    |||
    ||| @ bnds  Ordering witnesses on `k`. These are not erased.
    ||| @ elemL Proof that `k` is in a tree `l`.
    InLeft  : {0 sto : StrictOrdered kTy to} ->
              {0 l : BST sto vTy min (Mid x)} ->
              {0 r : BST sto vTy (Mid x) max} ->
              (bnds : (BndLT to min (Mid k), BndLT to (Mid k) (Mid x))) ->
              (elemL : Elem k l) ->
              Elem k (Node x v l r)
    ||| Proof that `k` is in the right subtree.
    |||
    ||| @ bnds  Ordering witnesses on `k`. These are not erased.
    ||| @ elemL Proof that `k` is in a tree `r`.
    InRight : {0 sto : StrictOrdered kTy to} ->
              {0 l : BST sto vTy min (Mid x)} ->
              {0 r : BST sto vTy (Mid x) max} ->
              (bnds : (BndLT to (Mid x) (Mid k), BndLT to (Mid k) max)) ->
              (elemR : Elem k r) ->
              Elem k (Node x v l r)

  export
  Uninhabited (Elem {sto} k (Empty prf)) where
    uninhabited Here        impossible
    uninhabited (InLeft _ _)  impossible
    uninhabited (InRight _ _) impossible

  ||| Proof that if `k` is an element of a tree and `k` precedes its root node, then `k` is an element
  ||| of its left subtree.
  elemInLeft : (sto : StrictOrdered kTy to) =>
               {k,x : kTy} ->
               {0 l : BST sto vTy min (Mid x)} ->
               {0 r : BST sto vTy (Mid x) max} ->
               BndLT to (Mid k) (Mid x) ->
               Elem {sto} k (Node x v l r) ->
               Elem {sto} k l
  elemInLeft {k} kx Here = absurd $ irreflexive (Mid k) kx
  elemInLeft _ (InLeft _ elemL) = elemL
  elemInLeft kx (InRight (xk, _) elemR) = absurd $ asymmetric (Mid k) (Mid x) kx xk

  ||| Proof that if `x` is an element of a tree and `x` follows its root node, then `x` is an element
  ||| of its right subtree.
  elemInRight : (sto : StrictOrdered kTy to) =>
                {k,x : kTy} ->
                {0 l : BST sto vTy min (Mid x)} ->
                {0 r : BST sto vTy (Mid x) max} ->
                BndLT to (Mid x) (Mid k) ->
                Elem {sto} k (Node x v l r) ->
                Elem {sto} k r
  elemInRight {k} xk Here = absurd $ irreflexive (Mid k) xk
  elemInRight xk (InLeft (_, kx) elemL) = absurd $ asymmetric (Mid k) (Mid x) kx xk
  elemInRight _ (InRight _ elemR) = elemR

  isElem' : {sto : StrictOrdered kTy to} ->
            (k : kTy) ->
            (BndLT to min (Mid k), BndLT to (Mid k) max) ->
            (t : BST sto vTy min max) ->
            Dec (Elem k t)
  isElem' _ _ (Empty _) = No absurd
  isElem' k (lk, ku) (Node x v l r) =
    case order (Mid k) (Mid x) of
        DecLT kx   => case isElem' k (lk, kx) l of
                            Yes prf => Yes $ InLeft (lk, kx) prf
                            No ctra => No $ ctra . (elemInLeft kx)
        DecEQ Refl => Yes Here
        DecGT xk   => case isElem' k (xk, ku) r of
                            Yes prf => Yes $ InRight (xk, ku) prf
                            No ctra => No $ ctra . (elemInRight xk)

  ||| Decide whether `k` is a key in the tree `t`.
  export
  isElem : {sto : StrictOrdered kTy to} ->
           (k : kTy) ->
           (t : BSTree sto vTy) ->
           Dec (Elem k t)
  isElem k t = isElem' k (BotLTMid, MidLTTop) t
