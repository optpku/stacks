/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Nonconstant
public import stacks_project.Chap111.Exercise_111_39_1_FieldPoint
public import stacks_project.Chap111.Exercise_111_42_8_Hypersurface
import Mathlib.Tactic.CrossRefAttribute

/-!
# Nonconstant maps from a hypersurface in P^3 to P^1

This file records the existence of a nonconstant morphism
`X ⟶ P^1_k` over `Spec k` for a hypersurface
`X = Proj(k[X 0, X 1, X 2, X 3] ⧸ (F)) ⊂ P^3_k` cut out by a factorization
`F = MvPolynomial.X 0 * G + MvPolynomial.X 1 * H` with no common zeros.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ProjectiveSpectrum
open Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Hypersurface

/-- The first two homogeneous coordinates of a 4-tuple. -/
def coordProj {L : Type u} (v : Fin 4 → L) : Fin 2 → L :=
  fun i ↦ v (i.castAdd 2)

/-- Evaluating `coordProj` recovers the corresponding entry of the 4-tuple. -/
theorem coordProj_apply {L : Type u} (v : Fin 4 → L) (i : Fin 2) :
    coordProj v i = v (i.castAdd 2) :=
  sorry

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
            Set (MvPolynomial (Fin 4) k)) = ∅ :=
  sorry

/-- A morphism `X ⟶ P^1_k` matches `(x0 : x1 : x2 : x3) ↦ (x0 : x1)` on
field-valued points of the hypersurface whenever `x0` or `x1` is nonzero. -/
def IsCoordinateProjectionOnFieldPoints {k : Type u} [Field k] {d : ℕ}
    (F : MvPolynomial (Fin 4) k) (hF : F ∈ ProjectiveSpace.grading k 3 d)
    (f : scheme 3 d F hF ⟶ ProjectiveSpace.scheme k 1) : Prop :=
  ∀ {L : Type u} [Field L] (φ : k →+* L)
    (v : Fin 4 → L) (hv : v ≠ 0) (w : Fin 2 → L) (hw : w ≠ 0),
    MvPolynomial.eval₂ φ v F = 0 → w 0 = v 0 → w 1 = v 1 →
      ∀ g : Spec (CommRingCat.of L) ⟶ scheme 3 d F hF,
        g ≫ closedImmersion 3 d F hF = ProjectiveSpace.homOf φ hv →
          g ≫ f = ProjectiveSpace.homOf φ hw

/-- Unfolding of `IsCoordinateProjectionOnFieldPoints`. -/
theorem IsCoordinateProjectionOnFieldPoints_iff {k : Type u} [Field k] {d : ℕ}
    (F : MvPolynomial (Fin 4) k) (hF : F ∈ ProjectiveSpace.grading k 3 d)
    (f : scheme 3 d F hF ⟶ ProjectiveSpace.scheme k 1) :
    IsCoordinateProjectionOnFieldPoints F hF f ↔
      ∀ {L : Type u} [Field L] (φ : k →+* L)
        (v : Fin 4 → L) (hv : v ≠ 0) (w : Fin 2 → L) (hw : w ≠ 0),
        MvPolynomial.eval₂ φ v F = 0 → w 0 = v 0 → w 1 = v 1 →
          ∀ g : Spec (CommRingCat.of L) ⟶ scheme 3 d F hF,
            g ≫ closedImmersion 3 d F hF = ProjectiveSpace.homOf φ hv →
              g ≫ f = ProjectiveSpace.homOf φ hw :=
  sorry

/-- A field-valued point of `P^3_k` on which `F` vanishes lifts along the closed
immersion of the hypersurface. -/
theorem exists_homOf_lift {k L : Type u} [Field k] [Field L] {d : ℕ}
    (F : MvPolynomial (Fin 4) k) (hF : F ∈ ProjectiveSpace.grading k 3 d)
    (φ : k →+* L) {v : Fin 4 → L} (hv : v ≠ 0)
    (hF0 : MvPolynomial.eval₂ φ v F = 0) :
    ∃ g : Spec (CommRingCat.of L) ⟶ scheme 3 d F hF,
      g ≫ closedImmersion 3 d F hF = ProjectiveSpace.homOf φ hv :=
  sorry

/-- Exercise 111.39.5: over a field `k`, let `X` be the hypersurface
`scheme 3 (d + 1) F hF`, i.e. `X = Proj(k[X 0, X 1, X 2, X 3] ⧸ (F)) ⊂ P^3_k`
with closed immersion `closedImmersion 3 (d + 1) F hF`. Assume
`F = MvPolynomial.X 0 * G + MvPolynomial.X 1 * H` for homogeneous `G`, `H` of
positive degree, and that `MvPolynomial.X 0`, `MvPolynomial.X 1`, `G`, `H` have
no common zeros in `P^3_k`. Then there exists a nonconstant morphism of schemes
over `Spec k` from `X` to `P^1_k` which on field-valued points
(Exercise 111.39.1) is given by `homOf` of `(x0, x1)` whenever `x0` or `x1` is
nonzero. -/
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
