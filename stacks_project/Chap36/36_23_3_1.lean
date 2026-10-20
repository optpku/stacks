/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.SingleSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open RingedSpace.Module.Derived
open RingedSpace.ModuleDerived
open RingedSite.Hom.DerivedAdjunction

universe u

/- 36.23.3.1: For `F : X.Modules` and `G : Y.Modules`, this is the canonical morphism
`RΓ(X, F) ⊗ᴸ_A RΓ(Y, G) ⟶ RΓ(X ×_S Y, p^*F ⊗ q^*G)`, where
`A = Scheme.globalSectionsRing S`. -/
@[stacks 0G49] #check
  (AlgebraicGeometry.Scheme.Modules.Kunneth.SingleSheaf.map :
    ∀ {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
      [KFlat.HomotopyTensorDescends S.toRingedSpace]
      [KFlat.TensorDescends S.toRingedSpace]
      [KFlat.IsLocalization S.toRingedSpace]
      [KFlat.HomotopyTensorDescends (Limits.pullback a b).toRingedSpace]
      [KFlat.TensorDescends (Limits.pullback a b).toRingedSpace]
      [KFlat.IsLocalization (Limits.pullback a b).toRingedSpace]
      [HomotopyCategory.KFlat.HasResolutions
        (Limits.pullback a b).toRingedSpace.Modules]
      [∀ G₁ G₂ : GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
        GradedObject.HasTensor G₁ G₂]
      [∀ G₁ G₂ G₃ : GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
        GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
      [∀ G₁ G₂ G₃ : GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
        GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
      [∀ G₁ G₂ G₃ G₄ :
        GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
        GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
      [HasPair (RingedSpace.opensRingedSiteHom a.toShHom)]
      [HasPair (RingedSpace.opensRingedSiteHom b.toShHom)]
      [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b).toShHom)]
      [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b).toShHom)]
      [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b ≫ a).toShHom)]
      [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b ≫ b).toShHom)]
      [HasPair (RingedSpace.opensRingedSiteHom
        ((Limits.pullback.fst a b).toShHom ≫ a.toShHom))]
      [HasPair (RingedSpace.opensRingedSiteHom
        ((Limits.pullback.snd a b).toShHom ≫ b.toShHom))]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison
        (Limits.pullback.fst a b).toShHom a.toShHom)]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison
        (Limits.pullback.snd a b).toShHom b.toShHom)]
      [(RingedSpace.modulePullbackDerived
        (Limits.pullback.fst a b ≫ a).toShHom).OplaxMonoidal]
      [MonoidalCategory (Tensor.globalSectionsDerived S.toRingedSpace)]
      [(GlobalSections.functor S.toRingedSpace).LaxMonoidal]
      (F : X.Modules) (G : Y.Modules),
      (GlobalSections.functor S.toRingedSpace).obj
            ((RingedSpace.moduleDerivedPushforward a.toShHom).obj
              ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ⊗
          (GlobalSections.functor S.toRingedSpace).obj
            ((RingedSpace.moduleDerivedPushforward b.toShHom).obj
              ((DerivedCategory.singleFunctor Y.Modules 0).obj G)) ⟶
        (GlobalSections.functor S.toRingedSpace).obj
          ((RingedSpace.moduleDerivedPushforward
            (Limits.pullback.fst a b ≫ a).toShHom).obj
              ((DerivedCategory.singleFunctor (Limits.pullback a b).Modules 0).obj
                (Scheme.Modules.externalTensorProduct a b F G))))
