module

public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.Cohomology

/-!
# Powers of sections on twisted cohomology

Vanishing of a degree-zero class after localization at a section is detected by the vanishing
of a suitable homogeneous component after multiplication by a power of that section.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.GradedSections

variable {X : Scheme.{u}}

/-- A degree-zero twisted-cohomology class vanishes after localization at a section exactly when
some power of the section annihilates its corresponding homogeneous component. -/
theorem localizedTwistedCohomologyMk_zero_eq_zero_iff
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ)
    (ξ : RingedSite.Hom.moduleGlobalCohomology
      (X := RingedSpace.opensRingedSite X.toRingedSpace) F p) :
    localizedTwistedCohomologyMk L F s p 0
        ((RingedSite.Hom.moduleGlobalCohomologyMap
          (X := RingedSpace.opensRingedSite X.toRingedSpace)
          ((ρ_ F).inv ≫
            (Iso.refl F ⊗ᵢ RingedSpace.unitIsoTensorUnit X.toRingedSpace).inv ≫
            (Iso.refl F ⊗ᵢ RingedSpace.InvertiblePower.zeroIso L).inv) p).hom ξ) = 0 ↔
      ∃ n : ℕ,
        DirectSum.component ℤ ℤ (twistedCohomologyDegree L F p) (n : ℤ)
            ((degreeOne L s : RingedSpace.GradedSections.ring L) ^ n •
              DirectSum.of (twistedCohomologyDegree L F p) (0 : ℤ)
                ((RingedSite.Hom.moduleGlobalCohomologyMap
                  (X := RingedSpace.opensRingedSite X.toRingedSpace)
                  ((ρ_ F).inv ≫
                    (Iso.refl F ⊗ᵢ RingedSpace.unitIsoTensorUnit X.toRingedSpace).inv ≫
                    (Iso.refl F ⊗ᵢ RingedSpace.InvertiblePower.zeroIso L).inv) p).hom ξ)) = 0 := sorry

end AlgebraicGeometry.Scheme.Modules.GradedSections
