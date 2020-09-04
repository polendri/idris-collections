module Collections.Set

||| Represents a set of elements of type `t`.
export
interface Set t s | s where
  ||| The empty set.
  empty : s
  ||| Create a singleton set.
  singleton : t -> s
  ||| Insert an element in a set. If the set already contains an element equal to the given value,
  ||| it is replaced with the new value.
  insert : t -> s -> s
