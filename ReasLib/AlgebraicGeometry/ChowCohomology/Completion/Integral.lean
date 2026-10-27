/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Theory
public import Mathlib.Algebra.Ring.MinimalAxioms
public import Mathlib.GroupTheory.Submonoid.Center
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The completed nonnegative Chow-cohomology ring

This module equips the product of the integral nonnegative homogeneous
Chow-cohomology groups with finite Cauchy-convolution multiplication and
constructs formal inverses of series whose constant coefficient is one.
-/

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChowCohomology.Nonnegative

variable {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
variable [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]

/-- The completed integral nonnegative Chow-cohomology carrier. -/
abbrev Completion : Type (u + 1) :=
  ∀ i : ℕ, degree δ p i

/-- `Completion` is the dependent product of all nonnegative Chow-cohomology degrees. -/
theorem completion_def : Completion δ p = (∀ i : ℕ, degree δ p i) := rfl

namespace Completion

/-- Two completed classes are equal when all coefficients agree. -/
@[ext]
theorem ext {a b : Completion δ p} (h : ∀ i, a i = b i) : a = b := funext h

/-- Transport an integral homogeneous class along an equality of degrees. -/
def castDegree {i j : ℕ} (h : i = j) (x : degree δ p i) : degree δ p j :=
  Eq.mp (congrArg (degree δ p) h) x

/-- Transport along reflexivity leaves an integral homogeneous class unchanged. -/
theorem castDegree_rfl {i : ℕ} (x : degree δ p i) :
    castDegree δ p rfl x = x := rfl

/-- The convolution unit is the degree-zero identity class. -/
def one : Completion δ p
  | 0 => ChowCohomology.one δ p
  | _ + 1 => 0

/-- The degree-zero coefficient of the convolution unit. -/
theorem one_apply_zero : one δ p 0 = ChowCohomology.one δ p := rfl

/-- Every positive-degree coefficient of the convolution unit vanishes. -/
theorem one_apply_succ (n : ℕ) : one δ p (n + 1) = 0 := rfl

/-- The homogeneous product indexed by an antidiagonal element, transported to its
specified total degree. -/
def antidiagonalMul (a b : Completion δ p) (n : ℕ)
    (ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n}) : degree δ p n :=
  castDegree δ p (Finset.mem_antidiagonal.mp ij.property)
    (Nonnegative.mul δ p (a ij.1.1) (b ij.1.2))

/-- Finite Cauchy convolution on completed integral Chow-cohomology classes. -/
def mul (a b : Completion δ p) : Completion δ p :=
  fun n ↦ (Finset.antidiagonal n).attach.sum (antidiagonalMul δ p a b n)

/-- Multiplication is coefficientwise finite Cauchy convolution. -/
theorem mul_apply (a b : Completion δ p) (n : ℕ) :
    mul δ p a b n =
      (Finset.antidiagonal n).attach.sum (antidiagonalMul δ p a b n) := rfl

/-- The canonical unit on completed integral nonnegative Chow cohomology. -/
noncomputable instance instOne : One (Completion δ p) := ⟨one δ p⟩

/-- The canonical convolution multiplication on completed integral nonnegative Chow cohomology. -/
noncomputable instance instMul : Mul (Completion δ p) := ⟨mul δ p⟩

private theorem homogeneous_castDegree {i j : ℕ} (h : i = j) (x : degree δ p i) :
    ChernClass.homogeneous δ p j (castDegree δ p h x) =
      ChernClass.homogeneous δ p i x := by
  subst j
  rfl

private theorem homogeneous_mul {i j : ℕ} (x : degree δ p i) (y : degree δ p j) :
    ChernClass.homogeneous δ p (i + j) (Nonnegative.mul δ p x y) =
      ChernClass.homogeneous δ p i x * ChernClass.homogeneous δ p j y :=
  (DirectSum.of_mul_of x y).symm

private theorem series_injective : Function.Injective
    (fun a : Completion δ p ↦
      PowerSeries.mk fun i ↦ ChernClass.homogeneous δ p i (a i)) := by
  intro a b h
  apply funext
  intro i
  apply DirectSum.of_injective i
  simpa only [PowerSeries.coeff_mk, ChernClass.homogeneous] using
    congrArg (PowerSeries.coeff i) h

private theorem series_mul (a b : Completion δ p) :
    (PowerSeries.mk fun i ↦ ChernClass.homogeneous δ p i ((a * b) i)) =
      (PowerSeries.mk fun i ↦ ChernClass.homogeneous δ p i (a i)) *
        (PowerSeries.mk fun i ↦ ChernClass.homogeneous δ p i (b i)) := by
  classical
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  change DirectSum.of (degree δ p) n
      ((Finset.antidiagonal n).attach.sum (antidiagonalMul δ p a b n)) = _
  rw [map_sum]
  simp_rw [PowerSeries.coeff_mk]
  conv_rhs => rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro ij hij
  exact (homogeneous_castDegree δ p (Finset.mem_antidiagonal.mp ij.property)
    (Nonnegative.mul δ p (a ij.1.1) (b ij.1.2))).trans
      (homogeneous_mul δ p (a ij.1.1) (b ij.1.2))

private theorem series_one :
    (PowerSeries.mk fun i ↦ ChernClass.homogeneous δ p i ((1 : Completion δ p) i)) =
      (1 : PowerSeries (Nonnegative.ring δ p)) := by
  apply PowerSeries.ext
  intro i
  cases i with
  | zero =>
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_zero_one]
    change DirectSum.of (degree δ p) 0 (ChowCohomology.one δ p) = 1
    rfl
  | succ i =>
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_one]
    change ChernClass.homogeneous δ p (i + 1) 0 = if i + 1 = 0 then 1 else 0
    simp [ChernClass.homogeneous]

private theorem series_add (a b : Completion δ p) :
    (PowerSeries.mk fun i ↦ ChernClass.homogeneous δ p i ((a + b) i)) =
      (PowerSeries.mk fun i ↦ ChernClass.homogeneous δ p i (a i)) +
        (PowerSeries.mk fun i ↦ ChernClass.homogeneous δ p i (b i)) := by
  apply PowerSeries.ext
  intro i
  simp [ChernClass.homogeneous]

/-- Convolution multiplication is associative. -/
theorem mul_assoc_axiom (a b c : Completion δ p) : a * b * c = a * (b * c) := by
  apply series_injective δ p
  simp only [series_mul, _root_.mul_assoc]

/-- The degree-zero identity is a left unit for convolution. -/
theorem one_mul_axiom (a : Completion δ p) : 1 * a = a := by
  apply series_injective δ p
  simpa only [series_mul, series_one, _root_.one_mul]

/-- The degree-zero identity is a right unit for convolution. -/
theorem mul_one_axiom (a : Completion δ p) : a * 1 = a := by
  apply series_injective δ p
  simpa only [series_mul, series_one, _root_.mul_one]

/-- Convolution distributes over addition in the right variable. -/
theorem mul_add_axiom (a b c : Completion δ p) :
    a * (b + c) = a * b + a * c := by
  apply series_injective δ p
  simp only [series_mul, series_add, _root_.mul_add]

/-- Convolution distributes over addition in the left variable. -/
theorem add_mul_axiom (a b c : Completion δ p) :
    (a + b) * c = a * c + b * c := by
  apply series_injective δ p
  simp only [series_mul, series_add, _root_.add_mul]

/-- The canonical ring structure on completed integral nonnegative Chow cohomology. -/
noncomputable instance instRing : Ring (Completion δ p) :=
  Ring.ofMinimalAxioms add_assoc zero_add neg_add_cancel
    (mul_assoc_axiom δ p) (one_mul_axiom δ p) (mul_one_axiom δ p)
      (mul_add_axiom δ p) (add_mul_axiom δ p)

/-- Regard a completed class as a formal power series in the finite-support
nonnegative Chow-cohomology ring. -/
def toPowerSeries (a : Completion δ p) : PowerSeries (Nonnegative.ring δ p) :=
  PowerSeries.mk fun i ↦ ChernClass.homogeneous δ p i (a i)

/-- The coefficient of `toPowerSeries a` is the homogeneous embedding of `a i`. -/
theorem toPowerSeries_coeff (a : Completion δ p) (i : ℕ) :
    PowerSeries.coeff i (toPowerSeries δ p a) =
      ChernClass.homogeneous δ p i (a i) := PowerSeries.coeff_mk i _

/-- The formal inverse of a completed class, obtained coefficientwise from the
power-series inverse with unit constant term. -/
def formalInverse (a : Completion δ p) : Completion δ p :=
  fun i ↦ DirectSum.component ℤ ℕ (degree δ p) i
    (PowerSeries.coeff i (PowerSeries.invOfUnit (toPowerSeries δ p a) 1))

/-- A formal-inverse coefficient is the matching homogeneous projection of the
power-series inverse. -/
theorem formalInverse_apply (a : Completion δ p) (i : ℕ) :
    formalInverse δ p a i = DirectSum.component ℤ ℕ (degree δ p) i
      (PowerSeries.coeff i (PowerSeries.invOfUnit (toPowerSeries δ p a) 1)) := rfl

private theorem homogeneous_projection {i j : ℕ} (h : i = j) (x : degree δ p i) :
    ChernClass.homogeneous δ p j
        (DirectSum.component ℤ ℕ (degree δ p) j (ChernClass.homogeneous δ p i x)) =
      ChernClass.homogeneous δ p i x := by
  subst j
  change DirectSum.of (degree δ p) i ((DirectSum.of (degree δ p) i x) i) = _
  rw [DirectSum.of_eq_same]
  rfl

private theorem formalInverse_homogeneous (a : Completion δ p) (i : ℕ) :
    ChernClass.homogeneous δ p i (formalInverse δ p a i) =
      PowerSeries.coeff i (PowerSeries.invOfUnit (toPowerSeries δ p a) 1) := by
  classical
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rw [formalInverse_apply]
    by_cases hi : i = 0
    · subst i
      simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]
      exact homogeneous_projection δ p rfl (ChowCohomology.one δ p)
    · have hrec :
          PowerSeries.coeff i (PowerSeries.invOfUnit (toPowerSeries δ p a) 1) =
            -∑ ij ∈ Finset.antidiagonal i,
              if ij.2 < i then
                PowerSeries.coeff ij.1 (toPowerSeries δ p a) *
                  PowerSeries.coeff ij.2
                    (PowerSeries.invOfUnit (toPowerSeries δ p a) 1)
              else 0 := by
        rw [PowerSeries.coeff_invOfUnit, if_neg hi]
        simp
      rw [hrec]
      simp only [ChernClass.homogeneous, map_neg, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro ij hij
      by_cases hj : ij.2 < i
      · rw [if_pos hj, toPowerSeries_coeff, ← ih ij.2 hj, ← homogeneous_mul]
        exact homogeneous_projection δ p (Finset.mem_antidiagonal.mp hij)
          (Nonnegative.mul δ p (a ij.1) (formalInverse δ p a ij.2))
      · simp [hj]

private theorem toPowerSeries_formalInverse (a : Completion δ p) :
    toPowerSeries δ p (formalInverse δ p a) =
      PowerSeries.invOfUnit (toPowerSeries δ p a) 1 := by
  apply PowerSeries.ext
  intro i
  rw [toPowerSeries_coeff]
  exact formalInverse_homogeneous δ p a i

/-- A completed class with unit constant coefficient multiplies its formal inverse to one. -/
theorem mul_formalInverse (a : Completion δ p)
    (ha : a 0 = ChowCohomology.one δ p) : a * formalInverse δ p a = 1 := by
  apply series_injective δ p
  dsimp only
  rw [series_mul, series_one]
  change toPowerSeries δ p a * toPowerSeries δ p (formalInverse δ p a) = 1
  rw [toPowerSeries_formalInverse]
  apply PowerSeries.mul_invOfUnit
  change ChernClass.homogeneous δ p 0 (a 0) = 1
  rw [ha]
  rfl

/-- The formal inverse of a completed class with unit constant coefficient multiplies it to one. -/
theorem formalInverse_mul (a : Completion δ p)
    (ha : a 0 = ChowCohomology.one δ p) : formalInverse δ p a * a = 1 := by
  apply series_injective δ p
  dsimp only
  rw [series_mul, series_one]
  change toPowerSeries δ p (formalInverse δ p a) * toPowerSeries δ p a = 1
  rw [toPowerSeries_formalInverse]
  apply PowerSeries.invOfUnit_mul
  change ChernClass.homogeneous δ p 0 (a 0) = 1
  rw [ha]
  rfl

/-- The formal inverse of a central completed class is central. -/
theorem formalInverse_mem_center (a : Completion δ p)
    (ha : a 0 = ChowCohomology.one δ p) (hcentral : a ∈ Set.center (Completion δ p)) :
    formalInverse δ p a ∈ Set.center (Completion δ p) := by
  apply Semigroup.mem_center_iff.mpr
  intro b
  calc
    b * formalInverse δ p a =
        (formalInverse δ p a * a) * (b * formalInverse δ p a) := by
      rw [formalInverse_mul δ p a ha, _root_.one_mul]
    _ = formalInverse δ p a * (a * b) * formalInverse δ p a := by
      simp only [_root_.mul_assoc]
    _ = formalInverse δ p a * (b * a) * formalInverse δ p a := by
      rw [(hcentral.comm b).eq]
    _ = formalInverse δ p a * b := by
      rw [_root_.mul_assoc, _root_.mul_assoc, mul_formalInverse δ p a ha,
        _root_.mul_one]

/-- Package a central completed class with constant coefficient one as a unit of the center. -/
def unitOf (a : Completion δ p) (ha : a 0 = ChowCohomology.one δ p)
    (hcentral : a ∈ Set.center (Completion δ p)) :
    (Submonoid.center (Completion δ p))ˣ where
  val := ⟨a, hcentral⟩
  inv := ⟨formalInverse δ p a, formalInverse_mem_center δ p a ha hcentral⟩
  val_inv := Subtype.ext (mul_formalInverse δ p a ha)
  inv_val := Subtype.ext (formalInverse_mul δ p a ha)

/-- The value of `unitOf` is the completed class supplied to it. -/
theorem unitOf_val (a : Completion δ p) (ha : a 0 = ChowCohomology.one δ p)
    (hcentral : a ∈ Set.center (Completion δ p)) :
    (unitOf δ p a ha hcentral).val.val = a := rfl

/-- The inverse value of `unitOf` is the named formal inverse. -/
theorem unitOf_inv (a : Completion δ p) (ha : a 0 = ChowCohomology.one δ p)
    (hcentral : a ∈ Set.center (Completion δ p)) :
    (unitOf δ p a ha hcentral).inv.val = formalInverse δ p a := rfl

end Completion

end AlgebraicGeometry.ChowCohomology.Nonnegative
