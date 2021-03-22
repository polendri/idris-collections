module Collections.BSTree.Set

import Collections.BSTree.Map as M
import Collections.BSTree.Set.Core
import Collections.BSTree.Set.Quantifiers
import Collections.Util.Bnd
import Data.Nat
import Data.Nat.Order.Strict
import Decidable.Order.Strict

import public Collections.BSTree.Set.Core

------------------
-- CONSTRUCTION --
------------------

||| The empty tree.
public export
empty : {0 sto : kTy -> kTy -> Type} ->
        {auto pre : StrictPreorder kTy sto} ->
        {auto tot : StrictOrdered kTy sto} ->
        BSTree sto {pre} {tot}
empty = M.empty

||| A tree with a single element.
public export
singleton : {0 sto : kTy -> kTy -> Type} ->
            {auto pre : StrictPreorder kTy sto} ->
            {auto tot : StrictOrdered kTy sto} ->
            (k : kTy) ->
            BSTree sto {pre} {tot}
singleton k = M.singleton k ()

---------------
-- INSERTION --
---------------

||| Insert an element in a tree. If the tree already contains an element equal to the given value,
||| it is replaced with the new value.
export
insert : {0 sto : kTy -> kTy -> Type} ->
         {pre : StrictPreorder kTy sto} ->
         {tot : StrictOrdered kTy sto} ->
         (k : kTy) ->
         BSTree sto {pre} {tot} ->
         BSTree sto {pre} {tot}
insert k t = M.insert k () t

--------------
-- QUERYING --
--------------

||| Is the tree empty?
export
null : BSTree sto {pre} {tot} -> Bool
null = M.null

||| The number of elements in the tree.
export
size : BSTree sto {pre} {tot} -> Nat
size = M.size

||| Is the element in the tree?
export
member : {0 sto : kTy -> kTy -> Type} ->
         {pre : StrictPreorder kTy sto} ->
         {tot : StrictOrdered kTy sto} ->
         (k : kTy) ->
         BSTree sto {pre} {tot} ->
         Bool
member = M.member

-----------------------
-- DELETION / UPDATE --
-----------------------

||| Delete an element from a tree. When the element is not in the tree, the original tree is
||| returned.
export
delete : {0 sto : kTy -> kTy -> Type} ->
         {pre : StrictPreorder kTy sto} ->
         {tot : StrictOrdered kTy sto} ->
         (k : kTy) ->
         BSTree sto {pre} {tot} ->
         BSTree sto {pre} {tot}
delete = M.delete
