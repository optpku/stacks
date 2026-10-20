/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface.FieldPoint
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Nonconstant
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory ProjectiveSpectrum
open Scheme.Hom
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Hypersurface

/-- The forms `MvPolynomial.X 0`, `MvPolynomial.X 1`, `G`, and `H` have no common
zeros in `P^3_k`. -/
def NoCommonZero {k : Type u} [Field k] (G H : MvPolynomial (Fin 4) k) : Prop :=
  ProjectiveSpectrum.zeroLocus (ProjectiveSpace.grading k 3)
      ({MvPolynomial.X 0, MvPolynomial.X 1, G, H} :
        Set (MvPolynomial (Fin 4) k)) = ∅

/-- `NoCommonZero G H` means the projective zero locus of
`{MvPolynomial.X 0, MvPolynomial.X 1, G, H}` in `P^3_k` is empty. -/
theorem NoCommonZero_iff {k : Type u} [Field k] (G H : MvPolynomial (Fin 4) k) :
    NoCommonZero G H ↔
      ProjectiveSpectrum.zeroLocus (ProjectiveSpace.grading k 3)
          ({MvPolynomial.X 0, MvPolynomial.X 1, G, H} :
            Set (MvPolynomial (Fin 4) k)) = ∅ := Iff.rfl

/-- A hypersurface in projective 3-space defined by `F = X₀G + X₁H`, where `G`
and `H` are homogeneous of the same positive degree and `X₀`, `X₁`, `G`, `H`
have no common projective zero, admits a nonconstant morphism over the base field
to projective 1-space extending the first-two-coordinate map on field-valued points. -/
@[stacks 02AB]
theorem exists_isNonconstant {k : Type u} [Field k] {d : ℕ}
    (F G H : MvPolynomial (Fin 4) k)
    (hF : F ∈ ProjectiveSpace.grading k 3 (d + 1))
    (hG : G ∈ ProjectiveSpace.grading k 3 d)
    (hH : H ∈ ProjectiveSpace.grading k 3 d) (hd : 0 < d)
    (hEq : F = MvPolynomial.X 0 * G + MvPolynomial.X 1 * H)
    (hZero : NoCommonZero G H) :
    ∃ f : Over.mk (hom 3 (d + 1) F hF) ⟶ ProjectiveSpace.schemeOver k 1,
      f.left.IsNonconstant ∧ IsCoordinateProjectionOnFieldPoints F hF f.left :=
  sorry

end AlgebraicGeometry.ProjectiveSpace.Hypersurface
