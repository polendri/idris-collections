module Collections.OrdMap.BSTree.Quantifiers

import Collections.OrdMap.BSTree.Core
import Collections.Util.Bnd
import Decidable.Order.Strict

||| A proof that a tree is non-empty.
public export
data NonEmpty : BST ord vTy min max -> Type where
  IsNode : {l : BST ord vTy min (Mid k)} ->
           {r : BST ord vTy (Mid k) max} ->
           NonEmpty (Node k v l r)
