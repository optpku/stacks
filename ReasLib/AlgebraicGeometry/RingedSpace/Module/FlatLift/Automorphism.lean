/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatLift
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Lift.Relative
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Automorphisms of flat lifts

Relative ideal-valued perturbations of the identity identify Ext⁰ with the
automorphisms of a flat lift inducing the identity on its specified reduction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian (Ext)
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Hom.ModuleMap (Lift)
open AlgebraicGeometry.RingedSpace.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom]
  [IsFirstOrderThickening U.hom] {g : T ⟶ U} {F : T.left.Modules}

/-- Every endomorphism of a relatively flat lift compatible with its specified
reduction is invertible. -/
theorem hom_isIso (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    [RingedSpace.Hom.IsFlat g.right] (L : FlatLift g F) (φ : Hom L L) :
    IsIso φ.hom := sorry

/-- For a strict morphism of first-order thickenings with flat upper morphism,
Ext⁰ with pulled-back base-ideal coefficients parametrizes the compatible
automorphisms of a flat lift by relative perturbation of the identity, using
explicit certificates for invertibility of the canonical source-ideal action
and of compatible endomorphisms. -/
def autEquivOf (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    [RingedSpace.Hom.IsFlat g.right] (L : FlatLift g F) [HasExt.{u} T.left.Modules]
    (hIdeal : IsIso (sourceIdealMulMap g L.module))
    (hAut : ∀ φ : Hom L L, IsIso φ.hom) :
    Ext F ((g.left^*).obj (idealModule U.hom) ⊗ F) 0 ≃
      {φ : Hom L L // IsIso φ.hom} := by
  let identity : Lift L.module L.module (𝟙 ((T.hom^*).obj L.module)) :=
    ⟨𝟙 L.module, (T.hom^*).map_id L.module⟩
  let parameterEquiv : (F ⟶ (g.left^*).obj (idealModule U.hom) ⊗ F) ≃
      ((T.hom^*).obj L.module ⟶
        (T.hom^*).obj L.module ⊗ (g.left^*).obj (idealModule U.hom)) :=
    (L.restrictIso.symm.homCongr
      (tensorIso (Iso.refl ((g.left^*).obj (idealModule U.hom))) L.restrictIso.symm)).trans
      ((Iso.refl ((T.hom^*).obj L.module)).homCongr
        ((modulesSymmetricCategory T.left).toBraidedCategory.braiding
          ((g.left^*).obj (idealModule U.hom)) ((T.hom^*).obj L.module)))
  let compatibleEquiv : Lift L.module L.module (𝟙 ((T.hom^*).obj L.module)) ≃
      Hom L L := {
    toFun := fun φ => ⟨φ.hom,
      (congrArg (fun k => k ≫ L.restrictIso.hom) φ.restrict).trans (Category.id_comp _)⟩
    invFun := fun φ => ⟨φ.hom,
      (cancel_mono L.restrictIso.hom).1
        (φ.restrictIso_hom.trans (Category.id_comp _).symm)⟩
    left_inv := by intro φ; cases φ; rfl
    right_inv := by intro φ; cases φ; rfl }
  let automorphismEquiv : Hom L L ≃ {φ : Hom L L // IsIso φ.hom} := {
    toFun := fun φ => ⟨φ, hAut φ⟩
    invFun := Subtype.val
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact Ext.homEquiv₀.trans <| parameterEquiv.trans <|
    (@ModuleMap.relativePerturbEquiv T U _ _ g L.module L.module
      (𝟙 ((T.hom^*).obj L.module))
      hIdeal identity).trans (compatibleEquiv.trans automorphismEquiv)

/-- Ext⁰ parametrizes compatible automorphisms of a flat lift by canonical
relative ideal-valued perturbations of the identity. -/
def autEquiv (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    [RingedSpace.Hom.IsFlat g.right] (L : FlatLift g F) [HasExt.{u} T.left.Modules] :
    Ext F ((g.left^*).obj (idealModule U.hom) ⊗ F) 0 ≃ Hom L L :=
  (autEquivOf hg L
    (@isIso_sourceIdealMulMap_of_isFlatOver T U _ _ g L.module L.isFlatOver hg)
    (hom_isIso hg L)).trans {
    toFun := Subtype.val
    invFun := fun φ => ⟨φ, hom_isIso hg L φ⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The automorphism associated to an Ext⁰ class has underlying map equal to the
identity plus its ideal-valued perturbation, transported through the specified
reduction isomorphism and the canonical relative ideal comparison. -/
theorem autEquiv_apply_hom (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    [RingedSpace.Hom.IsFlat g.right] (L : FlatLift g F) [HasExt.{u} T.left.Modules]
    (e : Ext F ((g.left^*).obj (idealModule U.hom) ⊗ F) 0) :
    (autEquiv hg L e).hom =
      𝟙 L.module + (homIdealMulEquiv T.hom L.module L.module
        ((L.restrictIso.hom ≫ Ext.homEquiv₀ (C := T.left.Modules) e ≫
          tensorHom (C := T.left.Modules) (𝟙 ((g.left^*).obj (idealModule U.hom)))
            L.restrictIso.inv ≫
          ((modulesSymmetricCategory T.left).toBraidedCategory.braiding
            ((g.left^*).obj (idealModule U.hom)) ((T.hom^*).obj L.module)).hom) ≫
          ModuleMap.sourceIdealTensorCompare g L.module) ≫
        idealMulι T.hom L.module : L.module ⟶ L.module) := sorry

/-- The automorphism associated to an Ext⁰ class has underlying map equal to the
identity plus its ideal-valued perturbation, transported through the specified
reduction isomorphism and the canonical relative ideal comparison. -/
theorem autEquivOf_apply_hom (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    [RingedSpace.Hom.IsFlat g.right] (L : FlatLift g F) [HasExt.{u} T.left.Modules]
    (hIdeal : IsIso (sourceIdealMulMap g L.module))
    (hAut : ∀ φ : Hom L L, IsIso φ.hom)
    (e : Ext F ((g.left^*).obj (idealModule U.hom) ⊗ F) 0) :
    (autEquivOf hg L hIdeal hAut e).val.hom =
      𝟙 L.module + (homIdealMulEquiv T.hom L.module L.module
        ((L.restrictIso.hom ≫ Ext.homEquiv₀ (C := T.left.Modules) e ≫
          tensorHom (C := T.left.Modules) (𝟙 ((g.left^*).obj (idealModule U.hom)))
            L.restrictIso.inv ≫
          ((modulesSymmetricCategory T.left).toBraidedCategory.braiding
            ((g.left^*).obj (idealModule U.hom)) ((T.hom^*).obj L.module)).hom) ≫
          ModuleMap.sourceIdealTensorCompare g L.module) ≫
        idealMulι T.hom L.module : L.module ⟶ L.module) := by
  exact autEquiv_apply_hom hg L e

end AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift
