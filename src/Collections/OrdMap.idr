module Collections.OrdMap

import Decidable.Order.Strict

-- This interface is modeled loosely on `Data.Map` in Haskell's `containers` package.
-- https://hackage.haskell.org/package/containers-0.6.4.1/docs/Data-Map-Strict.html
||| A map from keys to values (dictionaries), whose implementation depends on a strict ordering
||| property for the key type.
export
interface OrdMap (m : {0 kTy : Type} -> {0 sto : kTy -> kTy -> Type} -> (ord : StrictOrdered kTy sto) -> (0 vTy : Type) -> Type) where
  ------------------
  -- CONSTRUCTION --
  ------------------

  ||| The empty map.
  empty : (ord : StrictOrdered kTy sto) => m ord vTy
  ||| A map with a single element.
  singleton : (ord : StrictOrdered kTy sto) => (k : kTy) -> (v : vTy) -> m ord vTy

  ---------------
  -- INSERTION --
  ---------------

  ||| Insert a new key and value in the map. If the key is already present in the map, the
  ||| associated value is replaced with the supplied value.
  insert : {ord : StrictOrdered kTy sto} ->
           (k : kTy) ->
           (v : vTy) ->
           m ord vTy ->
           m ord vTy

  ||| Insert with a function, combining new value and old value. `insertWith f k v m` will insert
  ||| the pair `(k, v)` into `m` if `k` does not exist in the map. If the key does exist, the
  ||| function will insert the pair `(k, f new_v old_v)`.
  insertWith : {ord : StrictOrdered kTy sto} ->
               (f : vTy -> vTy -> vTy) ->
               (k : kTy) ->
               (v : vTy) ->
               m ord vTy ->
               m ord vTy

  --------------
  -- QUERYING --
  --------------

  ||| Predicate on a map being empty.
  null : {ord : StrictOrdered kTy sto} -> m ord vTy -> Bool
  ||| Counts the number of elements in the map.
  size : {ord : StrictOrdered kTy sto} -> m ord vTy -> Nat
  ||| Predicate on the membership of key `k` in the map.
  member : {ord : StrictOrdered kTy sto} ->
           (k : kTy) ->
           m ord vTy ->
           Bool
  ||| Looks up the value at a key `k` in the map.
  lookup : {ord : StrictOrdered kTy sto} ->
           (k : kTy) ->
           m ord vTy ->
           Maybe vTy
  ||| Looks up the value at key `k` or returns default value `def` when the key is not in the map.
  lookupOr : {ord : StrictOrdered kTy sto} ->
             (def : vTy) ->
             (k : kTy) ->
             m ord vTy ->
             vTy

  -----------------------
  -- DELETION / UPDATE --
  -----------------------

  ||| Delete a key and its value from the map. When the key is not a member of the map, the
  ||| original map is returned.
  delete : {ord : StrictOrdered kTy sto} ->
           (k : kTy) ->
           m ord vTy ->
           m ord vTy

  ||| Update a value at a specific key with the result of the provided function. When the key is not
  ||| a member of the map, the original map is returned.
  adjust : {ord : StrictOrdered kTy sto} ->
           (f : vTy -> vTy) ->
           (k : kTy) ->
           m ord vTy ->
           m ord vTy
