/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Even
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.GeometricCompactSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.LFunction
public import ReasLib.LinearAlgebra.Determinant.EulerFactor

/-!
# Cohomological L-functions of ℓ-adic sheaves

Signed determinant series of geometric Frobenius on compactly supported
cohomology and their equality with the closed-point Euler product.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry Polynomial

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

variable {k : Type u} [Field k] [Fintype k]
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom] [IsNoetherian X.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [Etale (Compactification.Of.ι P)]
variable [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [HasWeakSheafify (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u}]
variable [HasSheafify (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u})]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable (F : ZEllSheaf X.left ℓ)

/-- The cohomological Euler factor `det(1 - π_X^* T | H_c^i(X_k̄, F))` in
`PowerSeries ℚ_[ℓ]`. -/
def cohomologyEulerFactor (i : ℕ) : PowerSeries ℚ_[ℓ] :=
  Polynomial.toPowerSeries
    (LinearMap.charpolyRev (geometricFrobenius_cohomologyCompactSupportQEll P F i))

/-- Unfolding of `cohomologyEulerFactor` as the reverse characteristic polynomial
of `π_X^*` on `H_c^i(X_k̄, F ⊗ ℚ_[ℓ])`. -/
theorem cohomologyEulerFactor_spec (i : ℕ) :
    cohomologyEulerFactor P F i =
      Polynomial.toPowerSeries
        (LinearMap.charpolyRev
          (geometricFrobenius_cohomologyCompactSupportQEll P F i)) :=
  rfl

/-- The constant coefficient of each cohomological Euler factor is `1`. -/
theorem constantCoeff_cohomologyEulerFactor (i : ℕ) :
    PowerSeries.constantCoeff (cohomologyEulerFactor P F i) = 1 := by
  simp [cohomologyEulerFactor, LinearMap.charpolyRev,
    Polynomial.coeff_zero_eq_eval_zero]

/-- The signed cohomological Euler factor
`det(1 - π_X^* T | H_c^i(X_k̄, F))^{(-1)^{i+1}}`. Even degrees are inverted. -/
def signedCohomologyEulerFactor (i : ℕ) : PowerSeries ℚ_[ℓ] :=
  if Even i then PowerSeries.invOfUnit (cohomologyEulerFactor P F i) 1
  else cohomologyEulerFactor P F i

/-- Unfolding of the signed cohomological Euler factor into the even (inverse)
and odd (uninverted) cases. -/
theorem signedCohomologyEulerFactor_spec (i : ℕ) :
    signedCohomologyEulerFactor P F i =
      if Even i then PowerSeries.invOfUnit (cohomologyEulerFactor P F i) 1
      else cohomologyEulerFactor P F i :=
  rfl

/-- Zero-dimensional cohomology contributes the trivial signed Euler factor. -/
theorem signedCohomologyEulerFactor_eq_one_of_finrank_eq_zero (i : ℕ)
    (hi : Module.finrank ℚ_[ℓ] (geometricCohomologyCompactSupportQEll P F i) = 0) :
    signedCohomologyEulerFactor P F i = 1 := by
  haveI : Subsingleton (geometricCohomologyCompactSupportQEll P F i) :=
    Module.finrank_zero_iff.mp hi
  have hf : geometricFrobenius_cohomologyCompactSupportQEll P F i = 0 :=
    Subsingleton.elim _ _
  have he : cohomologyEulerFactor P F i = 1 := by
    simp [cohomologyEulerFactor, hf, LinearMap.charpolyRev, Matrix.charpolyRev]
  simp only [signedCohomologyEulerFactor, he]
  split_ifs
  · change PowerSeries.invOfUnit (1 : PowerSeries ℚ_[ℓ]) 1 = 1
    simpa only [mul_one] using
      (PowerSeries.invOfUnit_mul (1 : PowerSeries ℚ_[ℓ]) 1 rfl)
  · rfl

/-- The finite cohomological L-function
`∏_{i=0}^N det(1 - π_X^* T | H_c^i(X_k̄, F))^{(-1)^{i+1}}` in
`PowerSeries ℚ_[ℓ]`. -/
def cohomologicalLFunction (N : ℕ) : PowerSeries ℚ_[ℓ] :=
  ∏ i ∈ Finset.range (N + 1), signedCohomologyEulerFactor P F i

/-- Unfolding of `cohomologicalLFunction` as a finite product of signed
cohomological Euler factors. -/
theorem cohomologicalLFunction_spec (N : ℕ) :
    cohomologicalLFunction P F N =
      ∏ i ∈ Finset.range (N + 1), signedCohomologyEulerFactor P F i :=
  rfl

/-- Enlarging a vanishing bound does not change the cohomological L-function. -/
theorem cohomologicalLFunction_eq_of_vanishing {N M : ℕ} (hNM : N ≤ M)
    (hN : ∀ i, N < i →
      Module.finrank ℚ_[ℓ] (geometricCohomologyCompactSupportQEll P F i) = 0) :
    cohomologicalLFunction P F N = cohomologicalLFunction P F M := by
  apply Finset.prod_subset (Finset.range_mono (Nat.add_le_add_right hNM 1))
  intro i _ hi
  have hNi : N < i := Nat.lt_of_lt_of_le (Nat.lt_succ_self N)
    (Nat.le_of_not_gt (fun h ↦ hi (Finset.mem_range.mpr h)))
  exact signedCohomologyEulerFactor_eq_one_of_finrank_eq_zero P F i (hN i hNi)

/-- The cohomological L-function is independent of the choice of compactification. -/
theorem cohomologicalLFunction_independent
    (Q : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι Q)]
    [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction (Compactification.Of.ι Q)).op.HasLeftKanExtension G]
    [HasWeakSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u})]
    (N : ℕ) :
    cohomologicalLFunction P F N = cohomologicalLFunction Q F N :=
  sorry

/-- If ℓ is invertible in the finite base field, only finitely many signed
cohomological Euler factors differ from `1`. -/
theorem signedCohomologyEulerFactor_hasFiniteMulSupport (hℓ : (ℓ : k) ≠ 0) :
    Function.HasFiniteMulSupport (signedCohomologyEulerFactor P F) :=
  sorry

/-- A cohomological vanishing bound computes the product over all degrees by
the bounded cohomological L-function. -/
theorem cohomologicalLFunction_eq_finprod_of_vanishing (N : ℕ)
    (hN : ∀ i, N < i →
      Module.finrank ℚ_[ℓ] (geometricCohomologyCompactSupportQEll P F i) = 0) :
    cohomologicalLFunction P F N = ∏ᶠ i : ℕ, signedCohomologyEulerFactor P F i := by
  symm
  apply finprod_eq_prod_of_mulSupport_subset
  intro i hi
  apply Finset.mem_range.mpr
  by_contra h
  have hNi : N < i := Nat.lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.le_of_not_gt h)
  exact hi (signedCohomologyEulerFactor_eq_one_of_finrank_eq_zero P F i (hN i hNi))

/-- Over a finite field in which ℓ is invertible, the closed-point L-function
of a rational ℓ-adic sheaf equals the signed product of the determinant series
of geometric Frobenius on geometric compactly supported cohomology. -/
theorem lFunction_eq_prod_det_geometricFrobenius (hℓ : (ℓ : k) ≠ 0) :
    F.lFunction F.constructible = ∏ᶠ i : ℕ, signedCohomologyEulerFactor P F i :=
  sorry

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
