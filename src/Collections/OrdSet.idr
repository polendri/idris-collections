module Collections.OrdSet

import Decidable.Order.Strict

||| Represents a set of elements of type `t`, whose implementation depends on a strict ordering
||| property for the key type.
export
interface OrdSet (s : {0 t: Type} -> {0 sto : t -> t -> Type} -> (ord : StrictOrdered t sto) -> Type) where
  ------------------
  -- CONSTRUCTION --
  ------------------

  ||| The empty set.
  empty : (ord : StrictOrdered t sto) => s ord
  ||| Create a singleton set.
  singleton : (ord : StrictOrdered t sto) => (x : t) -> s ord
  ||| Create a set from a list of elements.
  fromList : (ord : StrictOrdered t sto) => (xs : List t) -> s ord

  ---------------
  -- INSERTION --
  ---------------

  ||| Insert an element in a set. If the set already contains an element equal to the given value,
  ||| it is replaced with the new value.
  insert : {ord : StrictOrdered t sto} ->
           (x : t) ->
           s ord ->
           s ord

  --------------
  -- DELETION --
  --------------

  ||| Delete an element from a set.
  delete : {ord : StrictOrdered t sto} ->
           (x : t) ->
           s ord ->
           s ord

  --------------
  -- QUERYING --
  --------------

  ||| Predicate on the membership of `x` in the set.
  member : {ord : StrictOrdered t sto} ->
           (x : t) ->
           s ord ->
           Bool
