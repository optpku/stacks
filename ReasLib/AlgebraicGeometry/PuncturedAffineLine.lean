module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The punctured affine line over `ℤ`

This file constructs the open immersion `Spec ℤ[t][1/t] ⟶ Spec ℤ[t]` and records
that it is a morphism of integral schemes, surjective on stalks, and not a closed
immersion.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.PuncturedAffineLine

/-- The affine line `Spec ℤ[t]`. -/
abbrev affineLine : Scheme :=
  Spec (CommRingCat.of (Polynomial ℤ))

/-- The punctured affine line `Spec ℤ[t][1/t]`. -/
abbrev puncturedAffineLine : Scheme :=
  Spec (CommRingCat.of (Localization.Away (Polynomial.X : Polynomial ℤ)))

/-- The canonical open immersion `Spec ℤ[t][1/t] ⟶ Spec ℤ[t]`. -/
abbrev hom : puncturedAffineLine ⟶ affineLine :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (Polynomial ℤ) (Localization.Away (Polynomial.X : Polynomial ℤ))))

/-- The affine line `Spec ℤ[t]` is an integral scheme. -/
instance instIsIntegralAffineLine : IsIntegral affineLine := inferInstance

/-- The punctured affine line `Spec ℤ[t][1/t]` is an integral scheme. -/
instance instIsIntegralPuncturedAffineLine : IsIntegral puncturedAffineLine := sorry

/-- The open immersion `hom` is surjective on stalks. -/
instance instSurjectiveOnStalks : SurjectiveOnStalks hom := inferInstance

/-- Each stalk map `𝒪_{affineLine, hom x} ⟶ 𝒪_{puncturedAffineLine, x}` is surjective. -/
theorem stalkMap_surjective (x : puncturedAffineLine) :
    Function.Surjective (hom.stalkMap x) := sorry

/-- The open immersion `hom` is not a closed immersion. -/
theorem not_isClosedImmersion : ¬ IsClosedImmersion hom := sorry

end AlgebraicGeometry.PuncturedAffineLine
