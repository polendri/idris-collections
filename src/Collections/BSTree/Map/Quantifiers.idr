module Collections.BSTree.Map.Quantifiers

import Collections.BSTree.Map.Core
import Collections.Util.Bnd
import Decidable.Order.Strict

||| A proof that a tree is non-empty.
public export
data NonEmpty : BST pre tot vTy min max -> Type where
  IsNode : {pre : StrictPreorder kTy sto} ->
           {tot : StrictOrdered kTy sto} ->
           {l : BST pre tot vTy min (Mid k)} ->
           {r : BST pre tot vTy (Mid k) max} ->
           NonEmpty (Node k v l r)
