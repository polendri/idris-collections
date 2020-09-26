module Collections.OrdMap.BSTree.Elem

import Collections.OrdMap.BSTree.Core
import Collections.Util.Bnd
import Decidable.Equality
import Decidable.Order.Strict

namespace Key
  ||| Proof that a key is contained in a `BSTree`.
  |||
  ||| @ k The key whose presence is being asserted
  ||| @ t The tree in which `k` is present
  public export
  data Elem : {ord : StrictOrdered kTy sto} ->
              (0 k : kTy) ->
              (0 t : BST ord vTy min max) ->
              Type where
    ||| Proof that `k` is at the root of the tree.
    Here    : Elem k (Node k v l r)
    ||| Proof that `k` is in the left subtree.
    |||
    ||| @ bnds  Ordering witnesses on `k`. These are not erased.
    ||| @ elemL Proof that `k` is in a tree `l`.
    InLeft  : {ord : StrictOrdered kTy sto} ->
              {0 l : BST ord vTy min (Mid x)} ->
              {0 r : BST ord vTy (Mid x) max} ->
              (bnds : (BndLT sto min (Mid k), BndLT sto (Mid k) (Mid x))) ->
              (elemL : Elem k l) ->
              Elem k (Node x v l r)
    ||| Proof that `k` is in the right subtree.
    |||
    ||| @ bnds  Ordering witnesses on `k`. These are not erased.
    ||| @ elemL Proof that `k` is in a tree `r`.
    InRight : {ord : StrictOrdered kTy sto} ->
              {0 l : BST ord vTy min (Mid x)} ->
              {0 r : BST ord vTy (Mid x) max} ->
              (bnds : (BndLT sto (Mid x) (Mid k), BndLT sto (Mid k) max)) ->
              (elemR : Elem k r) ->
              Elem k (Node x v l r)

  export
  Uninhabited (Elem {ord} k (Empty prf)) where
    uninhabited Here        impossible
    uninhabited (InLeft _ _)  impossible
    uninhabited (InRight _ _) impossible

  ||| Proof that if `k` is an element of a tree and `k` precedes its root node, then `k` is an element
  ||| of its left subtree.
  elemInLeft : (ord : StrictOrdered kTy sto) =>
               {k,x : kTy} ->
               {0 l : BST ord vTy min (Mid x)} ->
               {0 r : BST ord vTy (Mid x) max} ->
               BndLT sto (Mid k) (Mid x) ->
               Elem {ord} k (Node x v l r) ->
               Elem {ord} k l
  elemInLeft {k} kx Here = absurd $ irreflexive (Mid k) kx
  elemInLeft _ (InLeft _ elemL) = elemL
  elemInLeft kx (InRight (xk, _) elemR) = absurd $ asymmetric (Mid k) (Mid x) kx xk

  ||| Proof that if `x` is an element of a tree and `x` follows its root node, then `x` is an element
  ||| of its right subtree.
  elemInRight : (ord : StrictOrdered kTy sto) =>
                {k,x : kTy} ->
                {0 l : BST ord vTy min (Mid x)} ->
                {0 r : BST ord vTy (Mid x) max} ->
                BndLT sto (Mid x) (Mid k) ->
                Elem {ord} k (Node x v l r) ->
                Elem {ord} k r
  elemInRight {k} xk Here = absurd $ irreflexive (Mid k) xk
  elemInRight xk (InLeft (_, kx) elemL) = absurd $ asymmetric (Mid k) (Mid x) kx xk
  elemInRight _ (InRight _ elemR) = elemR

  isElem' : {ord : StrictOrdered kTy sto} ->
            (k : kTy) ->
            (BndLT sto min (Mid k), BndLT sto (Mid k) max) ->
            (t : BST ord vTy min max) ->
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
  isElem : {ord : StrictOrdered kTy sto} ->
           (k : kTy) ->
           (t : BSTree ord vTy) ->
           Dec (Elem k t)
  isElem k t = isElem' k (BotLTMid, MidLTTop) t

namespace Value
  ||| Proof that a value is contained in a `BSTree`.
  |||
  ||| @ v The key whose presence is being asserted
  ||| @ t The tree in which `v` is present
  public export
  data Elem : {ord : StrictOrdered kTy sto} ->
              (0 v : vTy) ->
              (0 t : BST ord vTy min max) ->
              Type where
    ||| Proof that `v` is at the root of the tree.
    Here    : Elem v (Node k v l r)
    ||| Proof that `v` is in the left subtree.
    |||
    ||| @ elemL Proof that `v` is in a tree `l`.
    InLeft  : {ord : StrictOrdered kTy sto} ->
              {0 l : BST ord vTy min (Mid k)} ->
              {0 r : BST ord vTy (Mid k) max} ->
              (elemL : Elem v l) ->
              Elem v (Node k x l r)
    ||| Proof that `v` is in the right subtree.
    |||
    ||| @ elemL Proof that `v` is in a tree `r`.
    InRight : {ord : StrictOrdered kTy sto} ->
              {0 l : BST ord vTy min (Mid k)} ->
              {0 r : BST ord vTy (Mid k) max} ->
              (elemR : Elem v r) ->
              Elem v (Node k x l r)

  export
  Uninhabited (Value.Elem {ord} v (Empty prf)) where
    uninhabited Here        impossible
    uninhabited (InLeft _)  impossible
    uninhabited (InRight _) impossible

  isElem' : DecEq vTy =>
            {ord : StrictOrdered kTy sto} ->
            (v : vTy) ->
            (t : BST ord vTy min max) ->
            Dec (Elem v t)
  isElem' _ (Empty _) = No absurd
  isElem' v (Node _ x l r) =
    case decEq v x of
         Yes Refl => Yes Here
         No  neq  => case isElem' v l of
                     Yes prf => Yes $ InLeft prf
                     No notL => case isElem' v r of
                                     Yes prf => Yes $ InRight prf
                                     No notR => No $ \case
                                                           InLeft  prf => absurd $ notL prf
                                                           Here        => absurd $ neq Refl
                                                           InRight prf => absurd $ notR prf

  ||| Decide whether `k` is a key in the tree `t`.
  export
  isElem : DecEq vTy =>
           {ord : StrictOrdered kTy sto} ->
           (v : vTy) ->
           (t : BSTree ord vTy) ->
           Dec (Elem v t)
  isElem v t = isElem' v t
