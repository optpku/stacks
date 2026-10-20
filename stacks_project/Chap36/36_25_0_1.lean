/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.InternalHom
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

universe u

/- 36.25.0.1: The canonical morphism
`R(a)_* RHom(K, K') ⊗ R(b)_* RHom(M, M') ⟶
  R(f)_* RHom(K ⊠ M, K' ⊠ M')`. -/
@[stacks 0FXY] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.Kunneth.homMap :
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
      [RingedSpace.ModuleDerived.KFlat.TensorDescends (pullback a b).toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization (pullback a b).toRingedSpace]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom a.toLRSHom.toShHom)]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom b.toLRSHom.toShHom)]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom (pullback.fst a b).toLRSHom.toShHom)]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom (pullback.snd a b).toLRSHom.toShHom)]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom (pullback.fst a b ≫ a).toLRSHom.toShHom)]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom
          ((pullback.fst a b).toLRSHom.toShHom ≫ a.toLRSHom.toShHom))]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom
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
      (K K' : RingedSpace.ModuleDerived X.toRingedSpace)
      (M M' : RingedSpace.ModuleDerived Y.toRingedSpace),
      (R(a.toLRSHom.toShHom)_*).obj ((ihom K).obj K') ⊗
          (R(b.toLRSHom.toShHom)_*).obj ((ihom M).obj M') ⟶
        (R((pullback.fst a b ≫ a).toLRSHom.toShHom)_*).obj
          ((ihom
            (AlgebraicGeometry.Scheme.ModuleDerived.Kunneth.externalTensorProduct a b K M)).obj
            (AlgebraicGeometry.Scheme.ModuleDerived.Kunneth.externalTensorProduct a b K' M')))
