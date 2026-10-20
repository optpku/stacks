module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coordinates on the standard charts of the projective line

This lightweight leaf owns the degree-zero homogeneous-localization rings, their distinguished
affine coordinates, and their canonical identifications with sections on the standard charts. It
is shared by overlap, restriction, and gluing computations.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLine

variable (R : Type u) [CommRing R]

namespace XChart

/-- The degree-zero homogeneous localization which is the coordinate ring of `D₊(X)`. -/
@[stacks 01JE "projective-line X-chart ring"]
abbrev ring := ProjectiveSpace.coordinateAway (R := R) 1 0

/-- The affine coordinate `Y / X` on the `X`-chart. -/
@[stacks 01JE "projective-line X-chart coordinate"]
noncomputable def coordinate : ring R :=
  HomogeneousLocalization.Away.isLocalizationElem
    (MvPolynomial.isHomogeneous_X R (0 : Fin 2))
    (MvPolynomial.isHomogeneous_X R (1 : Fin 2))

/-- The canonical homogeneous-localization identification of the `X`-chart section ring. -/
@[stacks 01JE "projective-line X-chart sections isomorphism"]
noncomputable abbrev sectionsIso :
    CommRingCat.of (ring R) ≅ Γ(scheme R, chartX R) :=
  ProjectiveSpace.coordinateBasicOpenIsoAway (R := R) 1 0

/-- The forward map of the canonical `X`-chart section-ring identification. -/
@[stacks 01JE "projective-line X-chart sections comparison"]
noncomputable abbrev sectionsComparison :
    CommRingCat.of (ring R) ⟶ Γ(scheme R, chartX R) :=
  (sectionsIso R).hom

/-- The canonical chart comparison agrees with Mathlib's `Proj.awayToSection` map. -/
@[simp, stacks 01JE "projective-line X-chart sections comparison readout"]
theorem sectionsComparison_eq_awayToSection :
    sectionsComparison R = Proj.awayToSection (grading R) (x R) := sorry

end XChart

namespace YChart

/-- The degree-zero homogeneous localization which is the coordinate ring of `D₊(Y)`. -/
@[stacks 01JE "projective-line Y-chart ring"]
abbrev ring := ProjectiveSpace.coordinateAway (R := R) 1 1

/-- The affine coordinate `X / Y` on the `Y`-chart. -/
@[stacks 01JE "projective-line Y-chart coordinate"]
noncomputable def coordinate : ring R :=
  HomogeneousLocalization.Away.isLocalizationElem
    (MvPolynomial.isHomogeneous_X R (1 : Fin 2))
    (MvPolynomial.isHomogeneous_X R (0 : Fin 2))

/-- The canonical homogeneous-localization identification of the `Y`-chart section ring. -/
@[stacks 01JE "projective-line Y-chart sections isomorphism"]
noncomputable abbrev sectionsIso :
    CommRingCat.of (ring R) ≅ Γ(scheme R, chartY R) :=
  ProjectiveSpace.coordinateBasicOpenIsoAway (R := R) 1 1

/-- The forward map of the canonical `Y`-chart section-ring identification. -/
@[stacks 01JE "projective-line Y-chart sections comparison"]
noncomputable abbrev sectionsComparison :
    CommRingCat.of (ring R) ⟶ Γ(scheme R, chartY R) :=
  (sectionsIso R).hom

/-- The canonical chart comparison agrees with Mathlib's `Proj.awayToSection` map. -/
@[simp, stacks 01JE "projective-line Y-chart sections comparison readout"]
theorem sectionsComparison_eq_awayToSection :
    sectionsComparison R = Proj.awayToSection (grading R) (y R) := sorry

end YChart
end AlgebraicGeometry.ProjectiveLine
