module Collections.OrdSet.BSTree

import Collections.OrdMap.BSTree as M
import Collections.OrdSet
import Collections.OrdSet.BSTree.Core
import Collections.Util.Bnd
import Decidable.Order.Strict

namespace BSTree
  ||| The empty set.
  export
  empty : (sto : StrictOrdered a to) => BSTree sto
  empty = M.BSTree.empty

  ||| Create a singleton set.
  export
  singleton : (sto : StrictOrdered a to) => (x : a) -> BSTree sto
  singleton x = M.BSTree.singleton x ()

  ||| Insert an element in a set. If the set already contains an element equal to the given value,
  ||| it is replaced with the new value.
  export
  insert : (sto : StrictOrdered a to) =>
           (x : a) ->
           BSTree sto ->
           BSTree sto
  insert x t = M.BSTree.insert x () t

  ||| Create a set from a list of elements.
  export
  fromList : (sto : StrictOrdered a to) =>
             (xs : List a) ->
             BSTree sto
  fromList [] = empty {sto}
  fromList (x::xs) = insert {sto} x $ fromList xs

export
OrdSet BSTree where
  empty {sto} = BSTree.empty {sto}
  singleton = BSTree.singleton
  fromList = BSTree.fromList
  insert = BSTree.insert
