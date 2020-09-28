module Collections.OrdMap.BSTree

import Collections.OrdMap
import Collections.OrdMap.BSTree.Quantifiers
import Collections.Util.Bnd
import Collections.Util.Erased
import Decidable.Order.Strict

import public Collections.OrdMap.BSTree.Core

namespace BSTree
  ------------------
  -- CONSTRUCTION --
  ------------------

  ||| The empty tree.
  export
  empty : (ord : StrictOrdered kTy sto) => BSTree ord vTy
  empty = Empty BotLTTop

  ||| A tree with a single element.
  export
  singleton : (ord : StrictOrdered kTy sto) => (k : kTy) -> (v : vTy) -> BSTree ord vTy
  singleton k v = Node k v (Empty BotLTMid) (Empty MidLTTop)

  ---------------
  -- INSERTION --
  ---------------

  insert' : {ord : StrictOrdered kTy sto} ->
            {0 min,max : Bnd kTy} ->
            (k : kTy) ->
            (v : vTy) ->
            (0 bnds : (BndLT sto min (Mid k), BndLT sto (Mid k) max)) ->
            BST ord vTy min max ->
            BST ord vTy min max
  insert' x vX (lx, xu) (Empty _) = Node x vX (Empty lx) (Empty xu)
  insert' x vX (lx, xu) (Node y vY l r) =
    case order {spo=BndLT sto} (Mid x) (Mid y) of
        DecLT xy   => Node y vY (insert' x vX (lx, xy) l) r
        DecEQ Refl => Node x vX l r
        DecGT yx   => Node y vY l (insert' x vX (yx, xu) r)

  ||| Insert a new key and value in the tree. If the key is already present in the tree, the
  ||| associated value is replaced with the supplied value.
  export
  insert : {ord : StrictOrdered kTy sto} ->
           (k : kTy) ->
           (v : vTy) ->
           BSTree ord vTy ->
           BSTree ord vTy
  insert k v t = insert' k v (BotLTMid, MidLTTop) t

  insertWith' : {ord : StrictOrdered kTy sto} ->
                {0 min,max : Bnd kTy} ->
                (f : vTy -> vTy -> vTy) ->
                (k : kTy) ->
                (v : vTy) ->
                (0 bnds : (BndLT sto min (Mid k), BndLT sto (Mid k) max)) ->
                BST ord vTy min max ->
                BST ord vTy min max
  insertWith' f x vX (lx, xu) (Empty _) = Node x vX (Empty lx) (Empty xu)
  insertWith' f x vX (lx, xu) (Node y vY l r) =
    case order {spo=BndLT sto} (Mid x) (Mid y) of
        DecLT xy   => Node y vY (insertWith' f x vX (lx, xy) l) r
        DecEQ Refl => Node x (f vX vY) l r
        DecGT yx   => Node y vY l (insertWith' f x vX (yx, xu) r)

  ||| Insert with a function, combining new value and old value. `insertWith f k v m` will insert
  ||| the pair `(k, v)` into `m` if `k` does not exist in the tree. If the key does exist, the
  ||| function will insert the pair `(k, f new_v old_v)`.
  export
  insertWith : {ord : StrictOrdered kTy sto} ->
               (f : vTy -> vTy -> vTy) ->
               (k : kTy) ->
               (v : vTy) ->
               BSTree ord vTy ->
               BSTree ord vTy
  insertWith f k v t = insertWith' f k v (BotLTMid, MidLTTop) t

  --------------
  -- QUERYING --
  --------------

  ||| Is the tree empty?
  export
  null : BSTree ord vTy -> Bool
  null (Empty _) = True
  null (Node _ _ _ _) = False

  ||| The number of elements in the tree.
  export
  size : BSTree ord vTy -> Nat
  size = size' where
    size' : BST ord vTy min max -> Nat
    size' (Empty _)      = 0
    size' (Node _ _ l r) = (size' l) + 1 + (size' r)

  ||| Is the key a member of the tree?
  export
  member : {ord : StrictOrdered kTy sto} ->
           (k : kTy) ->
           BSTree ord vTy ->
           Bool
  member = member' where
    member' : {ord : StrictOrdered kTy sto} ->
              (k : kTy) ->
              BST ord vTy min max ->
              Bool
    member' k (Empty _)      = False
    member' k (Node x v l r) = case order @{ord} k x of
                                    DecEQ _ => True
                                    _       => member' k l || member' k r

  ||| Lookup the value at a key in the tree.
  export
  lookup : {ord : StrictOrdered kTy sto} ->
           (k : kTy) ->
           BSTree ord vTy ->
           Maybe vTy
  lookup = lookup' where
    lookup' : {ord : StrictOrdered kTy sto} ->
              (k : kTy) ->
              BST ord vTy min max ->
              Maybe vTy
    lookup' k (Empty _) = Nothing
    lookup' k (Node x v l r) = case order @{ord} k x of
                                    DecLT _ => lookup' k l
                                    DecEQ _ => Just v
                                    DecGT _ => lookup' k r

  ||| Returns the value at key `k` or returns default value `def` when the key is not in the tree.
  export
  lookupOr : {ord : StrictOrdered kTy sto} ->
             (def : vTy) ->
             (k : kTy) ->
             BSTree ord vTy ->
             vTy
  lookupOr = lookupOr' where
    lookupOr' : {ord : StrictOrdered kTy sto} ->
                (def : vTy) ->
                (k : kTy) ->
                BST ord vTy min max ->
                vTy
    lookupOr' def k (Empty _)      = def
    lookupOr' def k (Node x v l r) = case order @{ord} k x of
                                          DecLT _ => lookupOr' def k l
                                          DecEQ _ => v
                                          DecGT _ => lookupOr' def k r

  -----------------------
  -- DELETION / UPDATE --
  -----------------------

  ||| Deletes the leftmost element of a tree, returning the key/value of the deleted element,
  ||| the ordering proof of the key w.r.t. `min`, and the updated tree.
  deleteLeftmost : {ord : StrictOrdered kTy sto} ->
                   (t : BST ord vTy min max) ->
                   (prf : NonEmpty t) ->
                   (kv : (kTy, vTy) ** (Erased (BndLT sto min (Mid (fst kv))), BST ord vTy (Mid (fst kv)) max))
  deleteLeftmost (Node k v (Empty mink) (Empty kmax)) IsNode = ((k, v) ** (MkErased mink, Empty kmax))
  deleteLeftmost (Node k v (Empty mink) (Empty kmax)) IsNode = ((k, v) ** (MkErased mink, Empty kmax))
  deleteLeftmost (Node k v (Empty mink) r@(Node _ _ _ _)) IsNode = ((k, v) ** (MkErased mink, r))
  deleteLeftmost (Node k v l@(Node _ _ _ _) r) IsNode =
    let ((k', v') ** (mink, l')) = deleteLeftmost l IsNode in ((k', v') ** (mink, Node k v l' r))

  delete' : {ord : StrictOrdered kTy sto} ->
            (x : kTy) ->
            BST ord vTy min max ->
            BST ord vTy min max
  delete' x t@(Empty _) = t
  delete' x (Node k v l r) =
    case order {spo=BndLT sto} (Mid x) (Mid k) of
        DecLT xy   => Node k v (delete' x l) r
        DecEQ Refl =>
          case (l, r) of
               (Empty minx,   Empty xmax      ) => Empty $ transitive min (Mid x) max minx xmax
               (Empty minx,   Node _ _ _ _    ) => extendMin minx r
               (Node _ _ _ _, Empty xmax      ) => extendMax xmax l
               (Node _ _ _ _, r@(Node _ _ _ _)) =>
                 let ((k', v') ** (MkErased xk, r')) = deleteLeftmost r IsNode in
                     Node k' v' (extendMax xk l) r'
        DecGT yx   => Node k v l (delete' x r)

  ||| Delete a key and its value from the tree. When the key is not a member of the tree, the
  ||| original tree is returned.
  export
  delete : {ord : StrictOrdered kTy sto} ->
           (k : kTy) ->
           BSTree ord vTy ->
           BSTree ord vTy
  delete = delete'

  ||| Update a value at a specific key with the result of the provided function. When the key is not
  ||| a member of the tree, the original tree is returned.
  export
  adjust : {ord : StrictOrdered kTy sto} ->
           (f : vTy -> vTy) ->
           (k : kTy) ->
           BSTree ord vTy ->
           BSTree ord vTy
  adjust = adjust' where
    adjust' : {ord : StrictOrdered kTy sto} ->
              (f : vTy -> vTy) ->
              (k : kTy) ->
              BST ord vTy min max ->
              BST ord vTy min max
    adjust' f x t@(Empty _) = t
    adjust' f x (Node k v l r) = case order @{ord} x k of
                                      DecLT _    => Node k v (adjust' f x l) r
                                      DecEQ Refl => Node k (f v) l r
                                      DecGT _    => Node k v l (adjust' f x r)

export
OrdMap BSTree where
  empty = BSTree.empty
  singleton = BSTree.singleton
  null = BSTree.null
  size = BSTree.size
  member = BSTree.member
  lookup = BSTree.lookup
  lookupOr = BSTree.lookupOr
  insert = BSTree.insert
  insertWith = BSTree.insertWith
  delete = BSTree.delete
  adjust = BSTree.adjust
