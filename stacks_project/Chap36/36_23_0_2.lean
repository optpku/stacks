/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.GlobalSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

universe u

/- 36.23.0.2: the canonical morphism
`RΓ(X, K) ⊗ᴸ_A RΓ(Y, M) ⟶ RΓ(X ×_S Y, Lp⁺K ⊗ᴸ Lq⁺M)` in `D(A)`, where
`A = Γ(S, ⊤)`, obtained by applying derived global sections to the scheme-level
Künneth morphism after the canonical tensor comparison. -/
@[stacks 0G7V] #check (AlgebraicGeometry.Scheme.Modules.Kunneth.globalMap :
  ∀ {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback a b).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends (Limits.pullback a b).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization (Limits.pullback a b).toRingedSpace]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom a.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom b.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b).toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b).toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b ≫ a).toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b ≫ b).toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom
        ((Limits.pullback.fst a b).toShHom ≫ a.toShHom))]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom
        ((Limits.pullback.snd a b).toShHom ≫ b.toShHom))]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison
      (Limits.pullback.fst a b).toShHom a.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison
      (Limits.pullback.snd a b).toShHom b.toShHom)]
    [(RingedSpace.modulePullbackDerived
      (Limits.pullback.fst a b ≫ a).toShHom).OplaxMonoidal]
    [MonoidalCategory
      (RingedSpace.ModuleDerived.Tensor.globalSectionsDerived S.toRingedSpace)]
    [(RingedSpace.Module.Derived.GlobalSections.functor S.toRingedSpace).LaxMonoidal]
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules),
    (RingedSpace.Module.Derived.GlobalSections.functor S.toRingedSpace).obj
          ((RingedSpace.moduleDerivedPushforward a.toShHom).obj K) ⊗
        (RingedSpace.Module.Derived.GlobalSections.functor S.toRingedSpace).obj
          ((RingedSpace.moduleDerivedPushforward b.toShHom).obj M) ⟶
      (RingedSpace.Module.Derived.GlobalSections.functor S.toRingedSpace).obj
        ((RingedSpace.moduleDerivedPushforward
          (Limits.pullback.fst a b ≫ a).toShHom).obj
            (AlgebraicGeometry.Scheme.ModuleDerived.Kunneth.externalTensorProduct a b K M)))
