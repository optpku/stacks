/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.SingleSheaf.Flat

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.MonoidalCategory ComplexShape
open RingedSpace.Module.Derived
open RingedSpace.ModuleDerived
open RingedSite.Hom.DerivedAdjunction

universe u

/- Lemma 36.23.4: over an affine base, the canonical degree-zero global Künneth morphism
of 36.23.3.1 is an isomorphism for relatively flat quasicoherent modules when the source
schemes are quasi-compact with affine absolute diagonal. -/
@[stacks 0FU4] #check
  (AlgebraicGeometry.Scheme.Modules.Kunneth.SingleSheaf.mapIsIso :
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
      [IsAffine S] [CompactSpace X] [CompactSpace Y]
      [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
      [IsAffineHom (prod.lift (𝟙 Y) (𝟙 Y))]
      (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
      [SheafOfModules.IsFlatOver F a.toShHom]
      [SheafOfModules.IsFlatOver G b.toShHom],
      IsIso (AlgebraicGeometry.Scheme.Modules.Kunneth.SingleSheaf.map a b F G))
