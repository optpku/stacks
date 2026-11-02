/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.FieldPoint.Coordinates
public import ReasLib.NumberTheory.Height.Projectivization

/-!
# Projective logarithmic height of scheme-valued points

The height is Mathlib's `Projectivization.logHeight` of the coordinate class
read from a scheme point. It is available for fields with admissible absolute
values, in particular number fields. This supplies projective heights as inputs
to the conditional associated-height API.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry LinearAlgebra.Projectivization

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The logarithmic height of an identity-base scheme point of projective space. -/
def logHeight {K : Type u} [Field K] [Height.AdmissibleAbsValues K] (n : ℕ)
    (f : Over.mk (Spec.map (CommRingCat.ofHom (RingHom.id K))) ⟶ schemeOver K n) : ℝ :=
  Projectivization.logHeight (coordinates (RingHom.id K) n f)

/-- The scheme-point height recovers the existing height of a homogeneous class. -/
theorem logHeight_homMk {K : Type u} [Field K] [Height.AdmissibleAbsValues K]
    (n : ℕ) (x : ℙ K (Fin (n + 1) → K)) :
    logHeight n (homMk (RingHom.id K) n x) = Projectivization.logHeight x := by
  rw [logHeight, coordinates_homMk]

/-- Evaluation on a homogeneous tuple uses Mathlib's existing tuple height. -/
theorem logHeight_homOf {K : Type u} [Field K] [Height.AdmissibleAbsValues K]
    (n : ℕ) {v : Fin (n + 1) → K} (hv : v ≠ 0) :
    logHeight n (Over.homMk (homOf (RingHom.id K) hv)
      (homOf_isOver (RingHom.id K) hv)) = Height.logHeight v := by
  rw [logHeight, coordinates_homOf, Projectivization.logHeight_mk]

/-- The projective height with the source used by the associated-height API. -/
def pointLogHeight {K : Type u} [Field K] [Height.AdmissibleAbsValues K] (n : ℕ)
    (f : SchemeOverField.point K ⟶ schemeOver K n) : ℝ :=
  Projectivization.logHeight (pointCoordinates n f)

/-- The chosen-source height evaluates on a homogeneous class by the existing formula. -/
theorem pointLogHeight_pointHomMk {K : Type u} [Field K] [Height.AdmissibleAbsValues K]
    (n : ℕ) (x : ℙ K (Fin (n + 1) → K)) :
    pointLogHeight n (pointHomMk n x) = Projectivization.logHeight x := by
  rw [pointLogHeight, pointCoordinates_pointHomMk]

/-- The chosen-source tuple computation agrees with Mathlib's tuple height. -/
theorem pointLogHeight_pointHomMk_mk {K : Type u} [Field K]
    [Height.AdmissibleAbsValues K] (n : ℕ) {v : Fin (n + 1) → K} (hv : v ≠ 0) :
    pointLogHeight n (pointHomMk n (Projectivization.mk K v hv)) = Height.logHeight v := by
  rw [pointLogHeight_pointHomMk, Projectivization.logHeight_mk]

/-- Over the rationals this is precisely the existing rational projective height. -/
theorem logHeight_homMk_rat (n : ℕ) (x : ℙ ℚ (Fin (n + 1) → ℚ)) :
    logHeight n (homMk (RingHom.id ℚ) n x) = Projectivization.rationalLogHeight n x :=
  logHeight_homMk n x

/-- The terminal-source rational specialization reuses `rationalLogHeight`. -/
theorem pointLogHeight_pointHomMk_rat (n : ℕ) (x : ℙ ℚ (Fin (n + 1) → ℚ)) :
    pointLogHeight n (pointHomMk n x) = Projectivization.rationalLogHeight n x :=
  pointLogHeight_pointHomMk n x

end AlgebraicGeometry.ProjectiveSpace
