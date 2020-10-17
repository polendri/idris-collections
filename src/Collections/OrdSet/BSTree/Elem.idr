module Collections.OrdSet.BSTree.Elem

import Collections.OrdMap.BSTree
import Collections.OrdMap.BSTree.Elem as M
import Collections.Util.Bnd
import Decidable.Order.Strict

||| Proof that an element is contained in a `BSTree`.
|||
||| @ x The key whose presence is being asserted
||| @ t The tree in which `x` is present
public export
Elem : {ord : StrictOrdered a sto} ->
       (0 x : a) ->
       (0 t : BST ord () min max) ->
       Type
Elem = M.Key.Elem

||| Decide whether `x` is an element of the tree `t`.
export
isElem : {ord : StrictOrdered a sto} ->
         (x : a) ->
         (t : BSTree ord ()) ->
         Dec (M.Key.Elem x t)
isElem = M.Key.isElem

||| Insert an element `x` in a set, and produce a membership proof for `x` in the updated tree.
||| If the set already contains an element equal to the given value, it is replaced with the new
||| value.
export
insertElem : {ord : StrictOrdered t sto} ->
             (x : t) ->
             BSTree ord () ->
             (t : BSTree ord () ** Key.Elem x t)
insertElem x t = let (t' ** (pk, _)) = M.insertElem x () t in (t' ** pk)
