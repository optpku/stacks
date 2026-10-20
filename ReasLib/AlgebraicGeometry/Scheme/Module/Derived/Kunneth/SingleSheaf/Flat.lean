/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.SingleSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.MonoidalCategory ComplexShape
open RingedSpace.Module.Derived
open RingedSpace.ModuleDerived
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Kunneth.SingleSheaf

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

variable [KFlat.HomotopyTensorDescends S.toRingedSpace]
variable [KFlat.TensorDescends S.toRingedSpace]
variable [KFlat.IsLocalization S.toRingedSpace]
variable [KFlat.HomotopyTensorDescends (Limits.pullback a b).toRingedSpace]
variable [KFlat.TensorDescends (Limits.pullback a b).toRingedSpace]
variable [KFlat.IsLocalization (Limits.pullback a b).toRingedSpace]
variable [HomotopyCategory.KFlat.HasResolutions
  (Limits.pullback a b).toRingedSpace.Modules]
variable [∀ G₁ G₂ : GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
  GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ :
  GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]

variable [HasPair (RingedSpace.opensRingedSiteHom a.toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom b.toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b).toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b).toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b ≫ a).toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b ≫ b).toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom
  ((Limits.pullback.fst a b).toShHom ≫ a.toShHom))]
variable [HasPair (RingedSpace.opensRingedSiteHom
  ((Limits.pullback.snd a b).toShHom ≫ b.toShHom))]

variable [IsIso (RingedSpace.modulePullbackDerived.compComparison
  (Limits.pullback.fst a b).toShHom a.toShHom)]
variable [IsIso (RingedSpace.modulePullbackDerived.compComparison
  (Limits.pullback.snd a b).toShHom b.toShHom)]
variable [(RingedSpace.modulePullbackDerived
  (Limits.pullback.fst a b ≫ a).toShHom).OplaxMonoidal]
variable [MonoidalCategory (Tensor.globalSectionsDerived S.toRingedSpace)]
variable [(GlobalSections.functor S.toRingedSpace).LaxMonoidal]

/-- Relative flatness of two module sheaves makes their canonical derived-to-underived
external tensor comparison invertible. -/
instance externalTensorComparison_isIso
    (F : X.Modules) (G : Y.Modules)
    [SheafOfModules.IsFlatOver F a.toShHom]
    [SheafOfModules.IsFlatOver G b.toShHom] :
    IsIso (externalTensorComparison a b F G) := sorry

/-- Over an affine base, the canonical degree-zero global Künneth morphism is invertible
for relatively flat quasicoherent modules on compact schemes with affine diagonal. -/
instance mapIsIso [IsAffine S] [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    [IsAffineHom (prod.lift (𝟙 Y) (𝟙 Y))]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [SheafOfModules.IsFlatOver F a.toShHom]
    [SheafOfModules.IsFlatOver G b.toShHom] :
    IsIso (map a b F G) := sorry

end AlgebraicGeometry.Scheme.Modules.Kunneth.SingleSheaf

end
