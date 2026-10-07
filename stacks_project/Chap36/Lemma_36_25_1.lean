module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.InternalHom.Perfect

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalClosed
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

/- Lemma 36.25.1: for quasi-compact and quasi-separated morphisms from Tor-independent
schemes over a common base, the canonical Ext Künneth morphism is an isomorphism when its
first inputs are perfect and its second inputs have quasicoherent cohomology. -/
@[stacks 0FXZ] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.Kunneth.homMapIsIso :
    ∀ {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends Y.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends Y.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization Y.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
        (pullback a b).toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends
        (pullback a b).toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization
        (pullback a b).toRingedSpace]
      [HasPair (RingedSpace.opensRingedSiteHom a.toLRSHom.toShHom)]
      [HasPair (RingedSpace.opensRingedSiteHom b.toLRSHom.toShHom)]
      [HasPair
        (RingedSpace.opensRingedSiteHom (pullback.fst a b).toLRSHom.toShHom)]
      [HasPair
        (RingedSpace.opensRingedSiteHom (pullback.snd a b).toLRSHom.toShHom)]
      [HasPair
        (RingedSpace.opensRingedSiteHom (pullback.fst a b ≫ a).toLRSHom.toShHom)]
      [HasPair
        (RingedSpace.opensRingedSiteHom (pullback.snd a b ≫ b).toLRSHom.toShHom)]
      [HasPair (RingedSpace.opensRingedSiteHom
        ((pullback.fst a b).toLRSHom.toShHom ≫ a.toLRSHom.toShHom))]
      [HasPair (RingedSpace.opensRingedSiteHom
        ((pullback.snd a b).toLRSHom.toShHom ≫ b.toLRSHom.toShHom))]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison
        (pullback.fst a b).toLRSHom.toShHom a.toLRSHom.toShHom)]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison
        (pullback.snd a b).toLRSHom.toShHom b.toLRSHom.toShHom)]
      [(RingedSpace.modulePullbackDerived
        (pullback.fst a b ≫ a).toLRSHom.toShHom).OplaxMonoidal]
      [(RingedSpace.modulePullbackDerived
        (pullback.fst a b).toLRSHom.toShHom).Monoidal]
      [(RingedSpace.modulePullbackDerived
        (pullback.snd a b).toLRSHom.toShHom).Monoidal]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
      [MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace)]
      [MonoidalClosed (RingedSpace.ModuleDerived (pullback a b).toRingedSpace)]
      [QuasiCompact a] [QuasiSeparated a]
      [QuasiCompact b] [QuasiSeparated b]
      (hTor : Scheme.TorIndependentOver (Over.mk a) (Over.mk b))
      (K : RingedSpace.ModuleDerived X.toRingedSpace)
      (K' : Scheme.ModuleDerived.Quasicoherent X)
      (M : RingedSpace.ModuleDerived Y.toRingedSpace)
      (M' : Scheme.ModuleDerived.Quasicoherent Y)
      (hK : RingedSpace.ModuleDerived.IsPerfect K)
      (hM : RingedSpace.ModuleDerived.IsPerfect M),
      IsIso (AlgebraicGeometry.Scheme.ModuleDerived.Kunneth.homMap
        a b K K'.obj M M'.obj))

end
