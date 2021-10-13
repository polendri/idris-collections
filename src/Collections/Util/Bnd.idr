module Collections.Util.Bnd

import Decidable.Equality
import Control.Relation
import Control.Order
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
export
midEq : Mid x = Mid y -> x = y
midEq Refl = Refl

||| Proof that if two `Mid` values are not equal, then their wrapped values are not equal
export
midNotEq : Not (Mid x = Mid y) -> Not (x = y)
midNotEq ctra prf = ctra $ cong Mid prf

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
Reflexive ty rel => Reflexive (Bnd ty) (BndLTE rel) where
  reflexive {x=Bot}   = BotLTEAll
  reflexive {x=Mid x} = MidLTEMid $ reflexive {x=x}
  reflexive {x=Top}   = AllLTETop

export
Transitive ty rel => Transitive (Bnd ty) (BndLTE rel) where
  transitive {x=Bot}                       BotLTEAll      yz             = BotLTEAll
  transitive {x=Mid x} {y=Mid y} {z=Mid z} (MidLTEMid xy) (MidLTEMid yz) = MidLTEMid $ transitive {x} {y} {z} xy yz
  transitive {x=Mid _} {y=Mid _} {z=Top}   (MidLTEMid xy) AllLTETop      = AllLTETop
  transitive           {y=Top}   {z=Top}   AllLTETop      AllLTETop      = AllLTETop

export
Antisymmetric ty rel => Antisymmetric (Bnd ty) (BndLTE rel) where
  antisymmetric {x=Bot}   {y=Bot}   BotLTEAll      BotLTEAll      = Refl
  antisymmetric {x=Mid x} {y=Mid y} (MidLTEMid xy) (MidLTEMid yx) = cong Mid $ antisymmetric {x} {y} xy yx
  antisymmetric {x=Top}   {y=Top}   AllLTETop      AllLTETop      = Refl

export
Connex ty rel => Connex (Bnd ty) (BndLTE rel) where
  connex {x=Bot}             _   = Left BotLTEAll
  connex           {y=Bot}   _   = Right BotLTEAll
  connex {x=Top}             _   = Right AllLTETop
  connex           {y=Top}   _   = Left AllLTETop
  connex {x=Mid x} {y=Mid y} prf = case connex {rel} {x} {y} (midNotEq prf) of
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
Transitive ty rel => Transitive (Bnd ty) (BndLT rel) where
  transitive {x=Bot}   {y=Mid _} {z=Mid _} BotLTMid      (MidLTMid _)  = BotLTMid
  transitive {x=Bot}   {y=Mid _} {z=Top}   BotLTMid      MidLTTop      = BotLTTop
  transitive {x=Bot}   {y=Top}             BotLTTop      BotLTMid      impossible
  transitive {x=Bot}   {y=Top}             BotLTTop      BotLTTop      impossible
  transitive {x=Bot}   {y=Top}             BotLTTop      (MidLTMid x)  impossible
  transitive {x=Bot}   {y=Top}             BotLTTop      MidLTTop      impossible
  transitive {x=Mid x} {y=Mid y} {z=Mid z} (MidLTMid xy) (MidLTMid yz) = MidLTMid $ transitive {x} {y} {z} xy yz
  transitive {x=Mid x} {y=Mid y} {z=Top}   (MidLTMid w)  MidLTTop      = MidLTTop
  transitive {x=Mid _} {y=Top}             MidLTTop      BotLTMid      impossible
  transitive {x=Mid _} {y=Top}             MidLTTop      BotLTTop      impossible
  transitive {x=Mid _} {y=Top}             MidLTTop      (MidLTMid y)  impossible
  transitive {x=Mid _} {y=Top}             MidLTTop      MidLTTop      impossible

export
Irreflexive ty rel => Irreflexive (Bnd ty) (BndLT rel) where
  irreflexive {x=Mid x} (MidLTMid xx) = irreflexive {x} xx

export
Asymmetric ty rel => Asymmetric (Bnd ty) (BndLT rel) where
  asymmetric BotLTMid BotLTMid impossible
  asymmetric BotLTMid BotLTTop impossible
  asymmetric BotLTMid (MidLTMid _) impossible
  asymmetric BotLTMid MidLTTop impossible
  asymmetric BotLTTop BotLTMid impossible
  asymmetric BotLTTop BotLTTop impossible
  asymmetric BotLTTop (MidLTMid _) impossible
  asymmetric BotLTTop MidLTTop impossible
  asymmetric (MidLTMid xy) (MidLTMid yx) = asymmetric {rel} xy yx
  asymmetric MidLTTop BotLTMid impossible
  asymmetric MidLTTop BotLTTop impossible
  asymmetric MidLTTop (MidLTMid _) impossible
  asymmetric MidLTTop MidLTTop impossible

export
StrictPreorder ty rel => StrictPreorder (Bnd ty) (BndLT rel) where

export
StrictOrdered ty rel => StrictOrdered (Bnd ty) (BndLT rel) where
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
