module Collections.Set.BSTree.Elem

import Collections.Set.BSTree
import Collections.Util.Bnd
import Decidable.Order.Strict

||| Proof that an element is contained in a `BSTree`.
|||
||| @ x The element whose presence is being asserted
||| @ t The tree in which `x` is present
public export
data Elem : {0 sto : StrictOrdered a to} ->
            (0 x : a) ->
            (0 t : BST sto min max) ->
            Type where
  ||| Proof that `x` is at the root of the tree.
  Here    : Elem x (Node x l r)
  ||| Proof that `x` is in the left subtree.
  |||
  ||| @ bnds  Ordering witnesses on `x`. These are not erased.
  ||| @ elemL Proof that `x` is in a tree `l`.
  InLeft  : {0 sto : StrictOrdered a to} ->
            {0 l : BST sto min (Mid y)} ->
            {0 r : BST sto (Mid y) max} ->
            (bnds : (BndLT to min (Mid x), BndLT to (Mid x) (Mid y))) ->
            (elemL : Elem x l) ->
            Elem x (Node y l r)
  ||| Proof that `x` is in the right subtree.
  |||
  ||| @ bnds  Ordering witnesses on `x`. These are not erased.
  ||| @ elemL Proof that `x` is in a tree `r`.
  InRight : {0 sto : StrictOrdered a to} ->
            {0 l : BST sto min (Mid y)} ->
            {0 r : BST sto (Mid y) max} ->
            (bnds : (BndLT to (Mid y) (Mid x), BndLT to (Mid x) max)) ->
            (elemR : Elem x r) ->
            Elem x (Node y l r)

export
Uninhabited (Elem {sto} x (Empty prf)) where
  uninhabited Here        impossible
  uninhabited (InLeft _ _)  impossible
  uninhabited (InRight _ _) impossible

||| Proof that if `x` is an element of a tree and `x` precedes its root node, then `x` is an element
||| of its left subtree.
elemInLeft : (sto : StrictOrdered a to) =>
             {x,y : a} ->
             {l : BST sto min (Mid y)} ->
             {r : BST sto (Mid y) max} ->
             BndLT to (Mid x) (Mid y) ->
             Elem {sto} x (Node y l r) ->
             Elem {sto} x l
elemInLeft {x} xy Here = absurd $ irreflexive (Mid x) xy
elemInLeft xy (InLeft _ elemL) = elemL
elemInLeft xy (InRight (yx, yu) elemR) = absurd $ asymmetric (Mid x) (Mid y) xy yx

||| Proof that if `x` is an element of a tree and `x` follows its root node, then `x` is an element
||| of its right subtree.
elemInRight : (sto : StrictOrdered a to) =>
              {x,y : a} ->
              {l : BST sto min (Mid y)} ->
              {r : BST sto (Mid y) max} ->
              BndLT to (Mid y) (Mid x) ->
              Elem {sto} x (Node y l r) ->
              Elem {sto} x r
elemInRight {x} yx Here = absurd $ irreflexive (Mid x) yx
elemInRight yx (InLeft (ly, xy) elemL) = absurd $ asymmetric (Mid x) (Mid y) xy yx
elemInRight yx (InRight _ elemR) = elemR

isElem' : {sto : StrictOrdered a to} ->
          (x : a) ->
          (BndLT to min (Mid x), BndLT to (Mid x) max) ->
          (t : BST sto min max) ->
          Dec (Elem x t)
isElem' _ _ (Empty _) = No absurd
isElem' x (lx, xu) (Node y l r) =
  case order (Mid x) (Mid y) of
       DecLT xy   => case isElem' x (lx, xy) l of
                          Yes prf => Yes $ InLeft (lx, xy) prf
                          No ctra => No $ ctra . (elemInLeft xy)
       DecEQ Refl => Yes Here
       DecGT yx   => case isElem' x (yx, xu) r of
                          Yes prf => Yes $ InRight (yx, xu) prf
                          No ctra => No $ ctra . (elemInRight yx)

||| Decide whether `x` is an element of the tree `t`.
export
isElem : {sto : StrictOrdered a to} ->
         (x : a) ->
         (t : BSTree sto) ->
         Dec (Elem x t)
isElem x t = isElem' x (BotLTMid, MidLTTop) t
