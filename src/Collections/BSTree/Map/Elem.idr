module Collections.BSTree.Map.Elem

import Collections.BSTree.Map.Core
import Collections.Util.Bnd
import Decidable.Equality
import Decidable.Order.Strict

namespace Key
  ||| Proof that a key is contained in a `BSTree`.
  |||
  ||| @ k The key whose presence is being asserted
  ||| @ t The tree in which `k` is present
  public export
  data Elem : {0 sto : kTy -> kTy -> Type} ->
              {pre : StrictPreorder kTy sto} ->
              {tot : StrictOrdered kTy sto} ->
              (k : kTy) ->
              (t : BST pre tot vTy min max) ->
              Type where
    [search k]
    ||| Proof that `k` is at the root of the tree.
    Here    : {0 l : BST pre tot vTy min (Mid k)} ->
              {0 r : BST pre tot vTy (Mid k) max} ->
              Elem k (Node k v l r)
    ||| Proof that `k` is in the left subtree.
    |||
    ||| @ bnds  Ordering witnesses on `k`. These are not erased.
    ||| @ elemL Proof that `k` is in a tree `l`.
    InLeft  : {0 sto : kTy -> kTy -> Type} ->
              {pre : StrictPreorder kTy sto} ->
              {tot : StrictOrdered kTy sto} ->
              {0 l : BST pre tot vTy min (Mid x)} ->
              {0 r : BST pre tot vTy (Mid x) max} ->
              (bnds : (BndLT sto min (Mid k), BndLT sto (Mid k) (Mid x))) ->
              (elemL : Elem k l) ->
              Elem k (Node x v l r)
    ||| Proof that `k` is in the right subtree.
    |||
    ||| @ bnds  Ordering witnesses on `k`. These are not erased.
    ||| @ elemL Proof that `k` is in a tree `r`.
    InRight : {0 sto : kTy -> kTy -> Type} ->
              {pre : StrictPreorder kTy sto} ->
              {tot : StrictOrdered kTy sto} ->
              {0 l : BST pre tot vTy min (Mid x)} ->
              {0 r : BST pre tot vTy (Mid x) max} ->
              (bnds : (BndLT sto (Mid x) (Mid k), BndLT sto (Mid k) max)) ->
              (elemR : Elem k r) ->
              Elem k (Node x v l r)

  export
  Uninhabited (Elem {pre} {tot} k (Empty prf)) where
    uninhabited Here        impossible
    uninhabited (InLeft _ _)  impossible
    uninhabited (InRight _ _) impossible

  ||| Proof that if `k` is an element of a tree and `k` precedes its root node, then `k` is an
  ||| element of its left subtree.
  elemInLeft : {0 sto : kTy -> kTy -> Type} ->
               {pre : StrictPreorder kTy sto} ->
               {tot : StrictOrdered kTy sto} ->
               {k,x : kTy} ->
               {l : BST pre tot vTy min (Mid x)} ->
               {r : BST pre tot vTy (Mid x) max} ->
               BndLT sto (Mid k) (Mid x) ->
               Elem k (Node x v l r) ->
               Elem k l
  elemInLeft {pre} {k} kx Here                    = absurd $ irreflexive (Mid k) kx
  elemInLeft           _  (InLeft _ elemL)        = elemL
  elemInLeft {pre}     kx (InRight (xk, _) elemR) =
    absurd $ asymmetric (Mid k) (Mid x) kx xk

  ||| Proof that if `x` is an element of a tree and `x` follows its root node, then `x` is an element
  ||| of its right subtree.
  elemInRight : {0 sto : kTy -> kTy -> Type} ->
                {pre : StrictPreorder kTy sto} ->
                {tot : StrictOrdered kTy sto} ->
                {k,x : kTy} ->
                {l : BST pre tot vTy min (Mid x)} ->
                {r : BST pre tot vTy (Mid x) max} ->
                BndLT sto (Mid x) (Mid k) ->
                Elem k (Node x v l r) ->
                Elem k r
  elemInRight {pre} {k} xk Here                   = absurd $ irreflexive (Mid k) xk
  elemInRight {pre}     xk (InLeft (_, kx) elemL) =
    absurd $ asymmetric (Mid k) (Mid x) kx xk
  elemInRight           _  (InRight _ elemR)      = elemR

  isElem' : {0 sto : kTy -> kTy -> Type} ->
            {pre : StrictPreorder kTy sto} ->
            {tot : StrictOrdered kTy sto} ->
            (k : kTy) ->
            (BndLT sto min (Mid k), BndLT sto (Mid k) max) ->
            (t : BST pre tot vTy min max) ->
            Dec (Elem k t)
  isElem' _ _ (Empty _) = No absurd
  isElem' {tot} k (lk, ku) (Node x v l r) =
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
  isElem : {0 sto : kTy -> kTy -> Type} ->
           {pre : StrictPreorder kTy sto} ->
           {tot : StrictOrdered kTy sto} ->
           (k : kTy) ->
           (t : BSTree sto {pre} {tot} vTy) ->
           Dec (Elem k t)
  isElem k t = isElem' k (BotLTMid, MidLTTop) t

namespace Value
  ||| Proof that a value is contained in a `BSTree`.
  |||
  ||| @ v The key whose presence is being asserted
  ||| @ t The tree in which `v` is present
  public export
  data Elem : {pre : StrictPreorder kTy sto} ->
              {tot : StrictOrdered kTy sto} ->
              (v : vTy) ->
              (t : BST pre tot vTy min max) ->
              Type where
    [search v]
    ||| Proof that `v` is at the root of the tree.
    Here    : Elem v (Node k v l r)
    ||| Proof that `v` is in the left subtree.
    |||
    ||| @ elemL Proof that `v` is in a tree `l`.
    InLeft  : {l : BST pre tot vTy min (Mid k)} ->
              {r : BST pre tot vTy (Mid k) max} ->
              (elemL : Value.Elem {pre} {tot} v l) ->
              Elem v (Node k x l r)
    ||| Proof that `v` is in the right subtree.
    |||
    ||| @ elemL Proof that `v` is in a tree `r`.
    InRight : {l : BST pre tot vTy min (Mid k)} ->
              {r : BST pre tot vTy (Mid k) max} ->
              (elemR : Value.Elem {pre} {tot} v r) ->
              Elem v (Node k x l r)

  export
  Uninhabited (Value.Elem v (Empty {pre} {tot} prf)) where
    uninhabited Here        impossible
    uninhabited (InLeft _)  impossible
    uninhabited (InRight _) impossible

  ||| Decide whether `v` is a value in the tree `t`.
  |||
  ||| Note that since the tree is structured by key, not by value, this is necessarily implemented
  ||| via an inefficient search.
  export
  isElem : DecEq vTy =>
           {pre : StrictPreorder kTy sto} ->
           {tot : StrictOrdered kTy sto} ->
           (v : vTy) ->
           (t : BSTree sto vTy) ->
           Dec (Value.Elem v t)
  isElem = isElem' where
    isElem' : (v : vTy) ->
              (t : BST pre tot vTy min max) ->
              Dec (Value.Elem v t)
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

insertElem' : {0 sto : kTy -> kTy -> Type} ->
              {pre : StrictPreorder kTy sto} ->
              {tot : StrictOrdered kTy sto} ->
              {0 min,max : Bnd kTy} ->
              (k : kTy) ->
              (v : vTy) ->
              (bnds : (BndLT sto min (Mid k), BndLT sto (Mid k) max)) ->
              (t : BST pre tot vTy min max) ->
              (t : BST pre tot vTy min max ** (Key.Elem k t, Value.Elem v t))
insertElem' x vX (lx, xu) (Empty _) =
  ((Node x vX (Empty lx) (Empty xu)) ** (Here, Here))
insertElem' {tot} x vX (lx, xu) (Node y vY l r) =
  case order (Mid x) (Mid y) of
      DecLT xy   => let bnd = (lx, xy)
                        (l' ** (pk, pv)) = insertElem' x vX bnd l in
                        (Node y vY l' r ** (InLeft bnd pk, InLeft pv))
      DecEQ Refl => (Node x vX l r ** (Here, Here))
      DecGT yx   => let bnd = (yx, xu)
                        (r' ** (pk, pv)) = insertElem' x vX bnd r in
                        (Node y vY l r' ** (InRight bnd pk, InRight pv))

||| Insert a new key `k` and value `v` in the tree, and produce membership proofs for `k` and `v` in
||| the updated tree. If the key is already present in the tree, the associated value is replaced
||| with the supplied value.
export
insertElem : {0 sto : kTy -> kTy -> Type} ->
             {pre : StrictPreorder kTy sto} ->
             {tot : StrictOrdered kTy sto} ->
             (k : kTy) ->
             (v : vTy) ->
             BSTree {pre} {tot} sto vTy ->
             (t : BSTree {pre} {tot} sto vTy ** (Key.Elem k t, Value.Elem v t))
insertElem k v t = insertElem' k v (BotLTMid, MidLTTop) t
