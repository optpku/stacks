/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.Cohomology.Power
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.NonvanishingOpen

/-!
# Twisted cohomology and affine nonvanishing opens

Positive-degree cohomology on the nonvanishing open of an invertible-module section vanishes
when that open is affine. On a quasi-compact and quasi-separated scheme, this implies that a
suitable power of the section annihilates every positive-degree cohomology class.
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

/-- Positive-degree cohomology of a quasicoherent module vanishes on an affine nonvanishing
open of a section of an invertible module. -/
theorem nonvanishingOpenCohomology_isZero_of_isAffineOpen
    (L : X.Modules) [hL : Invertible L]
    (F : X.Modules) [F.IsQuasicoherent] (s : Γ(L, ⊤))
    (hAffine : IsAffineOpen (hL.sectionNonvanishingOpen s))
    (p : ℕ) (hp : 0 < p) :
    CategoryTheory.Limits.IsZero (nonvanishingOpenCohomology L F s p) := sorry

/-- On a quasi-compact and quasi-separated scheme, a positive-degree cohomology class is
annihilated in the corresponding twist by some power of a section whose nonvanishing open is
affine. -/
theorem exists_twistedCohomologyPowSmul_eq_zero_of_isAffineOpen
    [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [hL : Invertible L]
    (F : X.Modules) [F.IsQuasicoherent] (s : Γ(L, ⊤))
    (hAffine : IsAffineOpen (hL.sectionNonvanishingOpen s))
    (p : ℕ) (hp : 0 < p)
    (ξ : RingedSite.Hom.moduleGlobalCohomology
      (X := RingedSpace.opensRingedSite X.toRingedSpace) F p) :
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
