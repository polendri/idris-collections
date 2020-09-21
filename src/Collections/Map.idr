module Collections.Map

||| A map from keys `k` to values `v`.
export
interface Map k v m | m where
  ||| The empty map.
  empty : m
  ||| A map with a single elemnt.
  singleton : k -> v -> m
  ||| Insert a new key and value in the map. If the key is already present in the map, the
  ||| associated value is replaced with the supplied value.
  insert : k -> v -> m -> m
