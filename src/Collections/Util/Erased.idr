module Collections.Util.Erased

||| A data type which wraps an erased value, so that it can be returned by a function for use in
||| another erased context.
public export
data Erased : (0 t : Type) -> Type where
  MkErased : (0 x : t) -> Erased t
