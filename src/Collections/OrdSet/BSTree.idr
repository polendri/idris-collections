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

  export
  insert : (sto : StrictOrdered a to) =>
           (x : a) ->
           BSTree sto ->
           BSTree sto
  insert x t = M.BSTree.insert x () t

export
OrdSet BSTree where
  empty = M.BSTree.empty
  singleton x = M.BSTree.singleton x ()
  insert x t = M.BSTree.insert x () t
