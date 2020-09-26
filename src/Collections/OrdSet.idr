module Collections.OrdSet

import Decidable.Order.Strict

||| Represents a set of elements of type `t`, whose implementation depends on a strict ordering
||| property for the key type.
export
interface (StrictOrdered t sto) => OrdSet (s : (t: Type) -> (sto : t -> t -> Type) -> Type) where
  ||| The empty set.
  empty : s t sto
  ||| Create a singleton set.
  singleton : (x : t) -> s t sto
  singleton x = insert x empty
  ||| Insert an element in a set. If the set already contains an element equal to the given value,
  ||| it is replaced with the new value.
  insert : (x : t) -> s t sto -> s t sto
