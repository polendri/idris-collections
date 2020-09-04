module Collections.Util.Bnd

import Decidable.Equality
import Decidable.Order
import Decidable.Order.Strict

||| Extends a type with `Bot` and `Top` values, making it a "bounded" type.
|||
||| Used for orderings in order to allow a value which precedes all other values (`Bot`), and a
||| value which follows all other values (`Top`).
public export
data Bnd : (0 a : Type) -> Type where
  Bot : Bnd a
  Mid : (x : a) -> Bnd a
  Top : Bnd a

export
Uninhabited (Bot = Mid x) where
  uninhabited Refl impossible

export
Uninhabited (Bot = Top) where
  uninhabited Refl impossible

export
Uninhabited (Mid x = Bot) where
  uninhabited Refl impossible

export
Uninhabited (Mid x = Top) where
  uninhabited Refl impossible

export
Uninhabited (Top = Bot) where
  uninhabited Refl impossible

export
Uninhabited (Top = Mid x) where
  uninhabited Refl impossible

||| Proof that if two `Mid` values are equal, then their wrapped values are equal
midEq : Mid x = Mid y -> x = y
midEq Refl = Refl

export
DecEq t => DecEq (Bnd t) where
  decEq Bot     Bot     = Yes Refl
  decEq Bot     (Mid _) = No absurd
  decEq Bot     Top     = No absurd
  decEq (Mid _) Bot     = No absurd
  decEq (Mid x) (Mid y) = case decEq x y of
                               Yes prf => Yes $ cong Mid prf
                               No ctra => No $ ctra . midEq
  decEq (Mid x) Top     = No absurd
  decEq Top     Bot     = No absurd
  decEq Top     (Mid _) = No absurd
  decEq Top     Top     = Yes Refl

||| Given a LTE (less than or equal) relation on `a`, produces an LTE relation extended to `Bnd a`
|||
||| @ o The ordering to extend
public export
data BndLTE : (o : a -> a -> Type) -> Bnd a -> Bnd a -> Type where
  ||| `Bot` is less than or equal to everything
  BotLTEAll : BndLTE o Bot y
  ||| Two `Mid`s are ordered iff their wrapped values are ordered
  MidLTEMid : {0 o : a -> a -> Type} -> o x y -> BndLTE o (Mid x) (Mid y)
  ||| Everything is less than or equal to `Top`
  AllLTETop : BndLTE o x Top

export
Preorder t po => Preorder (Bnd t) (BndLTE po) where
  transitive Bot     y       z       BotLTEAll      yz             = BotLTEAll
  transitive (Mid x) (Mid y) (Mid z) (MidLTEMid xy) (MidLTEMid yz) = MidLTEMid $ transitive x y z xy yz
  transitive (Mid x) (Mid y) Top     (MidLTEMid xy) AllLTETop      = AllLTETop
  transitive x       Top     Top     AllLTETop      AllLTETop      = AllLTETop
  reflexive Bot = BotLTEAll
  reflexive (Mid x) = MidLTEMid $ reflexive x
  reflexive Top = AllLTETop

export
Poset t po => Poset (Bnd t) (BndLTE po) where
  antisymmetric Bot     Bot     BotLTEAll      BotLTEAll      = Refl
  antisymmetric (Mid x) (Mid y) (MidLTEMid xy) (MidLTEMid yx) = cong Mid $ antisymmetric x y xy yx
  antisymmetric Top     Top     AllLTETop      AllLTETop      = Refl

export
Ordered t to => Ordered (Bnd t) (BndLTE to) where
  order Bot     y       = Left BotLTEAll
  order x       Bot     = Right BotLTEAll
  order Top     y       = Right AllLTETop
  order x       Top     = Left AllLTETop
  order (Mid x) (Mid y) = case order {to} x y of
                               Left  xy => Left  $ MidLTEMid xy
                               Right yx => Right $ MidLTEMid yx

||| Given a LT (less than) relation on `a`, produces a LT relation extended to `Bnd a`
|||
||| @ so The strict ordering to extend
public export
data BndLT : (so : a -> a -> Type) -> Bnd a -> Bnd a -> Type where
  BotLTMid : BndLT so Bot (Mid x)
  BotLTTop : BndLT so Bot Top
  MidLTMid : {0 so : a -> a -> Type} -> so x y -> BndLT so (Mid x) (Mid y)
  MidLTTop : BndLT so (Mid x) Top

export
StrictPreorder t spo => StrictPreorder (Bnd t) (BndLT spo) where
  transitive Bot     (Mid _) (Mid _) BotLTMid (MidLTMid _) = BotLTMid
  transitive Bot     (Mid _) Top     BotLTMid      MidLTTop      = BotLTTop
  transitive Bot     Top     _       BotLTTop      BotLTMid      impossible
  transitive Bot     Top     _       BotLTTop      BotLTTop      impossible
  transitive Bot     Top     _       BotLTTop      (MidLTMid x)  impossible
  transitive Bot     Top     _       BotLTTop      MidLTTop      impossible
  transitive (Mid x) (Mid y) (Mid z) (MidLTMid xy) (MidLTMid yz) = MidLTMid $ transitive x y z xy yz
  transitive (Mid x) (Mid y) Top     (MidLTMid w)  MidLTTop      = MidLTTop
  transitive (Mid _) Top     _       MidLTTop      BotLTMid      impossible
  transitive (Mid _) Top     _       MidLTTop      BotLTTop      impossible
  transitive (Mid _) Top     _       MidLTTop      (MidLTMid y)  impossible
  transitive (Mid _) Top     _       MidLTTop      MidLTTop      impossible
  irreflexive (Mid y) (MidLTMid yy) = irreflexive y yy

export
StrictOrdered t to => StrictOrdered (Bnd t) (BndLT to) where
  order Bot     Bot     = DecEQ Refl
  order Bot     (Mid _) = DecLT BotLTMid
  order Bot     Top     = DecLT BotLTTop
  order (Mid _) Bot     = DecGT BotLTMid
  order (Mid x) (Mid y) = case order x y of
                               DecLT xy => DecLT $ MidLTMid xy
                               DecEQ prf => DecEQ $ cong Mid prf
                               DecGT yx => DecGT $ MidLTMid yx
  order (Mid _) Top     = DecLT MidLTTop
  order Top     Bot     = DecGT BotLTTop
  order Top     (Mid _) = DecGT MidLTTop
  order Top     Top     = DecEQ Refl
