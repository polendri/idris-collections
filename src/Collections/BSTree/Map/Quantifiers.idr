module Collections.BSTree.Map.Quantifiers

import Collections.BSTree.Map.Core
import Collections.Util.Bnd
import Decidable.Order.Strict

||| A proof that a tree is non-empty.
public export
data NonEmpty : BST pre tot vTy mn mx -> Type where
  IsNode : {pre : StrictPreorder kTy sto} ->
           {tot : StrictOrdered kTy sto} ->
           {l : BST pre tot vTy mn (Mid k)} ->
           {r : BST pre tot vTy (Mid k) mx} ->
           NonEmpty (Node k v l r)
