module Collections.Util.KVP

import Decidable.Equality
import Decidable.Order

-- TODO docs
public export
data KVP : Type -> Type -> Type where
  ||| TODO docs
  MkKVP : {0 kt, vt : Type} -> (1 k : kt) -> (1 v : vt) -> KVP kt vt

eqValueIgnored1 : k1 = k2 -> MkKVP k1 v1 = MkKVP k2 v2
eqValueIgnored1 = believe_me

eqValueIgnored2 : MkKVP k1 v1 = MkKVP k2 v2 -> k1 = k2
eqValueIgnored2 = believe_me

export
DecEq kTy => DecEq (KVP kTy vTy) where
  decEq (MkKVP k1 v1) (MkKVP k2 v2) with (decEq k1 k2)
    decEq (MkKVP k1 v1) (MkKVP k2 v2) | Yes prf   = Yes $ eqValueIgnored1 prf
    decEq (MkKVP k1 v1) (MkKVP k2 v2) | No contra = No $ contra . eqValueIgnored2



-- export
-- Preorder kTy po => Preorder (KVP kTy vTy) (BndLTE po) where
--   transitive Bot     y       z       BotLTEAll      yz             = BotLTEAll
--   transitive (Mid x) (Mid y) (Mid z) (MidLTEMid xy) (MidLTEMid yz) = MidLTEMid $ transitive x y z xy yz
--   transitive (Mid x) (Mid y) Top     (MidLTEMid xy) AllLTETop      = AllLTETop
--   transitive x       Top     Top     AllLTETop      AllLTETop      = AllLTETop
--   reflexive Bot = BotLTEAll
--   reflexive (Mid x) = MidLTEMid $ reflexive x
--   reflexive Top = AllLTETop

-- export
-- Poset t po => Poset (Bnd t) (BndLTE po) where
--   antisymmetric Bot     Bot     BotLTEAll      BotLTEAll      = Refl
--   antisymmetric (Mid x) (Mid y) (MidLTEMid xy) (MidLTEMid yx) = cong Mid $ antisymmetric x y xy yx
--   antisymmetric Top     Top     AllLTETop      AllLTETop      = Refl

-- export
-- Ordered t to => Ordered (Bnd t) (BndLTE to) where
--   order Bot     y       = Left BotLTEAll
--   order x       Bot     = Right BotLTEAll
--   order Top     y       = Right AllLTETop
--   order x       Top     = Left AllLTETop
--   order (Mid x) (Mid y) = case order {to} x y of
--                                Left  xy => Left  $ MidLTEMid xy
--                                Right yx => Right $ MidLTEMid yx
