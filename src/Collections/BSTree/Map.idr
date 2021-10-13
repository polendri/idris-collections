module Collections.BSTree.Map

import Collections.BSTree.Map.Quantifiers
import Collections.Util.Bnd
import Collections.Util.Erased
import Data.Nat
import Data.Nat.Order.Strict
import Decidable.Order.Strict

import public Collections.BSTree.Map.Core

------------------
-- CONSTRUCTION --
------------------

||| The empty tree.
public export
empty : {0 rel : kTy -> kTy -> Type} ->
        {auto pre : StrictPreorder kTy rel} ->
        {auto tot : StrictOrdered kTy rel} ->
        BSTree rel {pre} {tot} vTy
empty = Empty BotLTTop

||| A tree with a single element.
public export
singleton : {0 rel : kTy -> kTy -> Type} ->
            {auto pre : StrictPreorder kTy rel} ->
            {auto tot : StrictOrdered kTy rel} ->
            (k : kTy) ->
            (v : vTy) ->
            BSTree rel {pre} {tot} vTy
singleton k v = Node k v (Empty BotLTMid) (Empty MidLTTop)

---------------
-- INSERTION --
---------------

insertWith' : {0 rel : kTy -> kTy -> Type} ->
              {pre : StrictPreorder kTy rel} ->
              {tot : StrictOrdered kTy rel} ->
              {0 mn,mx : Bnd kTy} ->
              (f : vTy -> vTy -> vTy) ->
              (k : kTy) ->
              (v : vTy) ->
              (0 bnds : (BndLT rel mn (Mid k), BndLT rel (Mid k) mx)) ->
              (t : BST pre tot vTy mn mx) ->
              BST pre tot vTy mn mx
insertWith' f x vX (lx, xu) (Empty _) = Node x vX (Empty lx) (Empty xu)
insertWith' {tot} f x vX (lx, xu) (Node y vY l r) =
  case order (Mid x) (Mid y) of
       DecLT xy   => Node y vY (insertWith' f x vX (lx, xy) l) r
       DecEQ Refl => Node x (f vX vY) l r
       DecGT yx   => Node y vY l (insertWith' f x vX (yx, xu) r)

||| Insert with a function, combining new value and old value. `insertWith f k v m` will insert
||| the pair `(k, v)` into `m` if `k` does not exist in the tree. If the key does exist, the
||| function will insert the pair `(k, f new_v old_v)`.
export
insertWith : {0 rel : kTy -> kTy -> Type} ->
             {pre : StrictPreorder kTy rel} ->
             {tot : StrictOrdered kTy rel} ->
             (f : vTy -> vTy -> vTy) ->
             (k : kTy) ->
             (v : vTy) ->
             BSTree rel {pre} {tot} vTy ->
             BSTree rel {pre} {tot} vTy
insertWith f k v t = insertWith' f k v (BotLTMid, MidLTTop) t

||| Insert a new key and value in the tree. If the key is already present in the tree, the
||| associated value is replaced with the supplied value.
export
insert : {0 rel : kTy -> kTy -> Type} ->
         {pre : StrictPreorder kTy rel} ->
         {tot : StrictOrdered kTy rel} ->
         (k : kTy) ->
         (v : vTy) ->
         BSTree rel {pre} {tot} vTy ->
         BSTree rel {pre} {tot} vTy
insert = insertWith const

--------------
-- QUERYING --
--------------

||| Is the tree empty?
export
null : BSTree rel {pre} {tot} vTy -> Bool
null (Empty _) = True
null (Node _ _ _ _) = False

size' : Nat -> (t: BST {rel} pre tot vTy mn mx) -> Nat
size' n (Empty _)      = n
size' n (Node _ _ l r) = size' (S (size' n l)) r

||| The number of elements in the tree.
export
size : BSTree rel {pre} {tot} vTy -> Nat
size t = size' 0 t where

member' : {0 rel : kTy -> kTy -> Type} ->
          {pre : StrictPreorder kTy rel} ->
          {tot : StrictOrdered kTy rel} ->
          (k : kTy) ->
          (t : BST pre tot vty mn mx) ->
          Bool
member'       k (Empty _)      = False
member' {tot} k (Node x v l r) = case order @{tot} k x of
                                      DecLT _ => member' k l
                                      DecEQ _ => True
                                      DecGT _ => member' k r

||| Is the key a member of the tree?
export
member : {0 rel : kTy -> kTy -> Type} ->
         {pre : StrictPreorder kTy rel} ->
         {tot : StrictOrdered kTy rel} ->
         (k : kTy) ->
         BSTree rel {pre} {tot} vTy ->
          Bool
member = member'

lookup' : {0 rel : kTy -> kTy -> Type} ->
          {pre : StrictPreorder kTy rel} ->
          {tot : StrictOrdered kTy rel} ->
          (k : kTy) ->
          (t : BST pre tot vTy mn mx) ->
          Maybe vTy
lookup'       k (Empty _)      = Nothing
lookup' {tot} k (Node x v l r) = case order @{tot} k x of
                                      DecLT _ => lookup' k l
                                      DecEQ _ => Just v
                                      DecGT _ => lookup' k r

||| Lookup the value at a key in the tree.
export
lookup : {0 rel : kTy -> kTy -> Type} ->
         {pre : StrictPreorder kTy rel} ->
         {tot : StrictOrdered kTy rel} ->
         (k : kTy) ->
         BSTree rel {pre} {tot} vTy ->
         Maybe vTy
lookup = lookup' where

lookupOr' : {0 rel : kTy -> kTy -> Type} ->
            {pre : StrictPreorder kTy rel} ->
            {tot : StrictOrdered kTy rel} ->
            (def : vTy) ->
            (k : kTy) ->
            (t : BST pre tot vTy mn mx) ->
            vTy
lookupOr'       def k (Empty _)      = def
lookupOr' {tot} def k (Node x v l r) = case order @{tot} k x of
                                            DecLT _ => lookupOr' def k l
                                            DecEQ _ => v
                                            DecGT _ => lookupOr' def k r

||| Returns the value at key `k` or returns default value `def` when the key is not in the tree.
export
lookupOr : {0 rel : kTy -> kTy -> Type} ->
           {pre : StrictPreorder kTy rel} ->
           {tot : StrictOrdered kTy rel} ->
           (def : vTy) ->
           (k : kTy) ->
           BSTree rel {pre} {tot} vTy ->
           vTy
lookupOr = lookupOr'

-----------------------
-- DELETION / UPDATE --
-----------------------

||| Deletes the leftmost element of a tree, returning the key/value of the deleted element,
||| the ordering proof of the key w.r.t. `mn`, and the updated tree.
deleteLeftmost : {0 rel : kTy -> kTy -> Type} ->
                 {pre : StrictPreorder kTy rel} ->
                 {tot : StrictOrdered kTy rel} ->
                 (t : BST pre tot vTy mn mx) ->
                 (prf : NonEmpty t) ->
                 (kv : (kTy, vTy) ** (Erased (BndLT rel mn (Mid (fst kv))),
                                     BST pre tot vTy (Mid (fst kv)) mx))
deleteLeftmost (Node k v (Empty mnk)     (Empty kmx)    ) IsNode =
  ((k, v) ** (MkErased mnk, Empty kmx))
deleteLeftmost (Node k v (Empty mnk)     r@(Node _ _ _ _)) IsNode =
  ((k, v) ** (MkErased mnk, r))
deleteLeftmost (Node k v l@(Node _ _ _ _) r               ) IsNode =
  let ((k', v') ** (mnk, l')) = deleteLeftmost l IsNode in
      ((k', v') ** (mnk, Node k v l' r))

delete' : {0 rel : kTy -> kTy -> Type} ->
          {pre : StrictPreorder kTy rel} ->
          {tot : StrictOrdered kTy rel} ->
          (k : kTy) ->
          (t : BST pre tot vTy mn mx) ->
          BST pre tot vTy mn mx
delete' x t@(Empty _) = t
delete' {pre} {tot} x (Node {mn} {mx} k v l r) =
  case order {spo=BndLT rel} (Mid x) (Mid k) of
       DecLT _    => Node k v (delete' x l) r
       DecEQ Refl =>
         case (l, r) of
              (Empty mnx,   Empty xmx      ) =>
                Empty $ transitive {rel=BndLT rel} {x=mn} {y=Mid x} {z=mx} mnx xmx
              (Empty mnx,   Node _ _ _ _     ) => extendMin mnx r
              (Node _ _ _ _, Empty xmx       ) => extendMax xmx l
              (Node _ _ _ _, r@(Node _ _ _ _)) =>
                let ((k', v') ** (MkErased xk, r')) = deleteLeftmost r IsNode in
                    Node k' v' (extendMax xk l) r'
       DecGT _    => Node k v l (delete' x r)

||| Delete a key and its value from the tree. When the key is not a member of the tree, the
||| original tree is returned.
export
delete : {0 rel : kTy -> kTy -> Type} ->
         {pre : StrictPreorder kTy rel} ->
         {tot : StrictOrdered kTy rel} ->
         (k : kTy) ->
         BSTree rel {pre} {tot} vTy ->
         BSTree rel {pre} {tot} vTy
delete = delete'

adjust' : {0 rel : kTy -> kTy -> Type} ->
          {pre : StrictPreorder kTy rel} ->
          {tot : StrictOrdered kTy rel} ->
          (f : vTy -> vTy) ->
          (k : kTy) ->
          BST pre tot vTy mn mx ->
          BST pre tot vTy mn mx
adjust'       f x t@(Empty _) = t
adjust' {tot} f x (Node k v l r) = case order @{tot} x k of
                                        DecLT _    => Node k v (adjust' f x l) r
                                        DecEQ Refl => Node k (f v) l r
                                        DecGT _    => Node k v l (adjust' f x r)

||| Update a value at a specific key with the result of the provided function. When the key is not
||| a member of the tree, the original tree is returned.
export
adjust : {0 rel : kTy -> kTy -> Type} ->
         {pre : StrictPreorder kTy rel} ->
         {tot : StrictOrdered kTy rel} ->
         (f : vTy -> vTy) ->
         (k : kTy) ->
         BSTree rel {pre} {tot} vTy ->
         BSTree rel {pre} {tot} vTy
adjust = adjust'

-----------
-- TESTS --
-----------

empty_isNull : null (empty {rel=LT} {vTy=Bool}) = True
empty_isNull = Refl

singleton_notNull : null (singleton {rel=LT} 2 False) = False
singleton_notNull = Refl

singleton_equivToInsertEmpty : singleton 5 'a' = insert 5 'a' (empty {rel=LT})
singleton_equivToInsertEmpty = Refl

member_missingKeyLeft_returnsFalse : member 1 (singleton {rel=LT} 2 'a') = False
member_missingKeyLeft_returnsFalse = Refl

member_missingKeyRight_returnsFalse : member 3 (singleton {rel=LT} 2 'a') = False
member_missingKeyRight_returnsFalse = Refl

member_keyInRoot_returnsTrue : member 2 (singleton {rel=LT} 2 'a') = True
member_keyInRoot_returnsTrue = Refl

member_keyInRight_returnsTrue : member 5 (insert 5 True (singleton {rel=LT} 2 False)) = True
member_keyInRight_returnsTrue = Refl

member_keyInLeft_returnsTrue : member 1 (insert 1 True (singleton {rel=LT} 2 False)) = True
member_keyInLeft_returnsTrue = Refl

lookup_keyExists_returnsJust : lookup 2 (insert 5 'b' (singleton {rel=LT} 2 'a')) = Just 'a'
lookup_keyExists_returnsJust = Refl

lookup_keyMissing_returnsNothing : lookup 9 (insert 5 'b' (singleton {rel=LT} 2 'a')) = Nothing
lookup_keyMissing_returnsNothing = Refl

lookupOr_keyExists_returnsValue : lookupOr 'c' 2 (insert 5 'a' (singleton {rel=LT} 2 'b')) = 'b'
lookupOr_keyExists_returnsValue = Refl

lookupOr_keyMissing_returnsDefault : lookupOr 'c' 9 (insert 5 'a' (singleton {rel=LT} 2 'b')) = 'c'
lookupOr_keyMissing_returnsDefault = Refl

delete_keyMissing_treeUnchanged : delete 1 (singleton {rel=LT} 2 'a') = singleton {rel=LT} 2 'a'
delete_keyMissing_treeUnchanged = Refl

delete_keyExists_removesKey : delete 2 (insert 1 'a' (singleton {rel=LT} 2 'b')) = singleton {rel=LT} 1 'a'
delete_keyExists_removesKey = Refl

adjust_keyMissing_treeUnchanged : adjust (\_ => 'b') 1 (singleton {rel=LT} 2 'a') = singleton {rel=LT} 2 'a'
adjust_keyMissing_treeUnchanged = Refl

adjust_keyExists_treeUpdated : adjust (\_ => 'c') 2 (insert 1 'a' (singleton {rel=LT} 2 'b')) =
                                insert 1 'a' (singleton {rel=LT} 2 'c')
adjust_keyExists_treeUpdated = Refl
