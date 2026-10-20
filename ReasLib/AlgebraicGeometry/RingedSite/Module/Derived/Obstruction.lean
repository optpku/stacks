/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CanonicalClass
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings

/-!
# Vanishing of the obstruction to lifting a derived module

For a locally surjective square-zero morphism of structure sheaves, the canonical obstruction
of a bounded-above derived module vanishes exactly when it admits a bounded-above lift.
-/

@[expose] public section

open CategoryTheory
open DerivedCategory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.SameSite (pullbackDerived)

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

-- Local instance justification (defeq pin): this pins free HasDerivedCategory inference to the standard model already fixed by RingedSiteDerived and canonicalClass.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]
variable {𝒪 𝒪₀ : Sheaf J CommRingCat.{w}}
variable (π : 𝒪 ⟶ 𝒪₀)
variable [Sheaf.IsLocallySurjective π]
variable [(restrictionAlong π).IsRightAdjoint]
variable (h_sq : KernelIdeal.IsSquareZero π)
variable [SheafOfModules.Localization.HasLowerShriek.{w} (ringSheaf J 𝒪)]
variable [DerivedTensor.Right.Has (C := ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀)]
variable [DerivedTensor.Bifunctor.Has (C := ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀)]

/-- For a locally surjective square-zero morphism of structure sheaves, the canonical
degree-two obstruction of a bounded-above derived module vanishes if and only if it is
isomorphic to the derived extension of scalars of a bounded-above derived module. -/
theorem canonicalClass_eq_zero_iff
    (K₀ : RingedSiteDerived.{u, v, w, w} J 𝒪₀) (hK : K₀.IsBoundedAbove) :
    canonicalClass π h_sq K₀ hK = 0 ↔
      ∃ K : RingedSiteDerived.{u, v, w, w} J 𝒪,
        K.IsBoundedAbove ∧
          IsIsomorphic ((pullbackDerived π).obj K) K₀ := sorry

end RingedSite.Hom.ModuleDerived
