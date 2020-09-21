module Collections.Set.BSTree.Elem

import Collections.Map.BSTree
import Collections.Map.BSTree.Elem as M
import Collections.Util.Bnd
import Decidable.Order.Strict

||| Proof that an element is contained in a `BSTree`.
|||
||| @ x The key whose presence is being asserted
||| @ t The tree in which `x` is present
public export
Elem : {0 sto : StrictOrdered a to} ->
       (0 x : a) ->
       (0 t : BST sto () min max) ->
       Type
Elem = M.Key.Elem

||| Decide whether `x` is an element of the tree `t`.
export
isElem : {sto : StrictOrdered a to} ->
         (x : a) ->
         (t : BSTree sto ()) ->
         Dec (M.Key.Elem x t)
isElem = M.Key.isElem
