/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Valuation.PrimeChain
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalizationQuotient
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Criteria
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace LocalizationQuotientCoprod

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
variable (p : Ideal A) [p.IsPrime]

/-- The localization-quotient coproduct morphism does not lift valuation-ring
extensions when the prime is neither the zero ideal nor the maximal ideal. -/
theorem not_valuationRingExtensionLift (hp_bot : p ≠ ⊥)
    (hp_max : p ≠ IsLocalRing.maximalIdeal A) :
    ¬ ValuationRingExtensionLift (hom A p) := sorry

/-- The singleton family of a localization-quotient coproduct morphism is not a
V covering when the prime is neither the zero ideal nor the maximal ideal. -/
theorem not_isVCovering_singleton (hp_bot : p ≠ ⊥)
    (hp_max : p ≠ IsLocalRing.maximalIdeal A) :
    ¬ IsVCovering (Spec (CommRingCat.of A))
      (fun _ : PUnit ↦ source A p) (fun _ ↦ hom A p) := sorry

end LocalizationQuotientCoprod

/-- There exists a universally submersive morphism of affine schemes whose
singleton family is not a V covering. -/
theorem exists_affine_universallySubmersive_not_isVCovering :
    ∃ (X Y : Scheme.{u}) (_ : IsAffine X) (_ : IsAffine Y) (f : X ⟶ Y),
      UniversallySubmersive f ∧
        ¬ IsVCovering Y (fun _ : PUnit ↦ X) (fun _ ↦ f) := sorry

end AlgebraicGeometry
