/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
import Mathlib.Tactic.CrossRefAttribute

/-!
# The standard overlap of the projective-line charts

This file owns the common basic open `D₊(XY)`, its homogeneous-localization coordinate ring, and
the inverse transition coordinates `Y / X` and `X / Y`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLine

variable (R : Type u) [CommRing R]

/-- The common overlap of the two standard affine charts, canonically presented as `D₊(XY)`. -/
@[stacks 01JE "standard projective-line chart overlap"]
abbrev overlap : (scheme R).Opens :=
  ProjectiveSpace.basicOpen (R := R) 1 (x R * y R)

/-- The product `XY` has degree two in the standard grading. -/
@[stacks 01JE "projective-line overlap product degree"]
theorem x_mul_y_mem_grading_two : x R * y R ∈ grading R 2 := by
  exact SetLike.mul_mem_graded (A := grading R) (i := 1) (j := 1)
    (MvPolynomial.isHomogeneous_X R (0 : Fin 2))
    (MvPolynomial.isHomogeneous_X R (1 : Fin 2))

/-- The square `Y²` has degree two in the standard grading. -/
@[stacks 01JE "projective-line overlap Y-square degree"]
theorem y_sq_mem_grading_two : y R ^ 2 ∈ grading R 2 := by
  exact MvPolynomial.isHomogeneous_X_pow (R := R) (1 : Fin 2) 2

/-- The square `X²` has degree two in the standard grading. -/
@[stacks 01JE "projective-line overlap X-square degree"]
theorem x_sq_mem_grading_two : x R ^ 2 ∈ grading R 2 := by
  exact MvPolynomial.isHomogeneous_X_pow (R := R) (0 : Fin 2) 2

/-- The canonical basic-open presentation of the overlap equals the intersection of the two
coordinate charts. -/
@[simp, stacks 01JE "projective-line overlap intersection"]
theorem overlap_eq_chart_inf : overlap R = chartX R ⊓ chartY R := by
  exact ProjectiveSpectrum.basicOpen_mul (grading R) (x R) (y R)

namespace Overlap

/-- The degree-zero homogeneous localization which is the coordinate ring of
`D₊(X) ∩ D₊(Y)`. -/
@[stacks 01JE "projective-line overlap ring"]
abbrev ring := HomogeneousLocalization.Away (grading R) (x R * y R)

/-- The `X`-chart coordinate `Y / X`, represented over the common denominator `XY`. -/
@[stacks 01JE "projective-line overlap X-chart coordinate"]
noncomputable def xChartCoordinate : ring R :=
  HomogeneousLocalization.Away.isLocalizationElem
    (SetLike.mul_mem_graded
      (MvPolynomial.isHomogeneous_X R (0 : Fin 2))
      (MvPolynomial.isHomogeneous_X R (1 : Fin 2)))
    (MvPolynomial.isHomogeneous_X R (1 : Fin 2))

/-- The `Y`-chart coordinate `X / Y`, represented over the common denominator `XY`. -/
@[stacks 01JE "projective-line overlap Y-chart coordinate"]
noncomputable def yChartCoordinate : ring R :=
  HomogeneousLocalization.Away.isLocalizationElem
    (SetLike.mul_mem_graded
      (MvPolynomial.isHomogeneous_X R (0 : Fin 2))
      (MvPolynomial.isHomogeneous_X R (1 : Fin 2)))
    (MvPolynomial.isHomogeneous_X R (0 : Fin 2))

/-- The canonical isomorphism from the degree-zero homogeneous localization away from `XY` to
sections on the common overlap. -/
@[stacks 01JE "projective line chart overlap isomorphism"]
noncomputable def sectionsIso :
    CommRingCat.of (ring R) ≅ Γ(scheme R, overlap R) :=
  Proj.basicOpenIsoAway (grading R) (x R * y R)
    (SetLike.mul_mem_graded
      (MvPolynomial.isHomogeneous_X R (0 : Fin 2))
      (MvPolynomial.isHomogeneous_X R (1 : Fin 2)))
    (Nat.zero_lt_succ 1)

/-- The forward map of the canonical common-overlap sections isomorphism. -/
@[stacks 01JE "projective line chart overlap comparison"]
noncomputable abbrev sectionsComparison :
    CommRingCat.of (ring R) ⟶ Γ(scheme R, overlap R) :=
  (sectionsIso R).hom

/-- The canonical overlap comparison agrees with Mathlib's `Proj.awayToSection` map. -/
@[simp, stacks 01JE "projective-line overlap sections comparison readout"]
theorem sectionsComparison_eq_awayToSection :
    sectionsComparison R = Proj.awayToSection (grading R) (x R * y R) := by
  rfl

private theorem coordinates_mul : xChartCoordinate R * yChartCoordinate R = 1 := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (x R * y R))
  simp only [xChartCoordinate, yChartCoordinate,
    HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, mul_one]
  ring

/-- The `X`-chart coordinate is a unit on the common overlap. -/
@[stacks 01JE "projective-line overlap X-coordinate unit"]
theorem xChartCoordinate_isUnit : IsUnit (xChartCoordinate R) := by
  exact isUnit_iff_exists_inv.mpr ⟨yChartCoordinate R, coordinates_mul R⟩

/-- The `Y`-chart coordinate is a unit on the common overlap. -/
@[stacks 01JE "projective-line overlap Y-coordinate unit"]
theorem yChartCoordinate_isUnit : IsUnit (yChartCoordinate R) := by
  refine isUnit_iff_exists_inv.mpr ⟨xChartCoordinate R, ?_⟩
  rw [mul_comm, coordinates_mul]

/-- On the common overlap the affine coordinates satisfy `(Y / X) * (X / Y) = 1`. -/
@[simp, stacks 01JE "projective line chart transition"]
theorem xChartCoordinate_mul_yChartCoordinate :
    xChartCoordinate R * yChartCoordinate R = 1 := by
  exact coordinates_mul R

end Overlap
end AlgebraicGeometry.ProjectiveLine
