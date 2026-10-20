/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.Rational
public import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# The rational completed nonnegative Chow-cohomology ring

This module equips the product of the rationalized nonnegative homogeneous
Chow-cohomology groups with finite Cauchy-convolution multiplication.
-/

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.ChowCohomology.Nonnegative

variable {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
variable [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]

/-- The rationalization of degree-`i` nonnegative Chow cohomology. -/
abbrev RationalDegree (i : ℕ) : Type (u + 1) :=
  TensorProduct ℤ (degree δ p i) ℚ

/-- `RationalDegree` is the tensor product of the integral degree with `ℚ`. -/
theorem rationalDegree_def (i : ℕ) :
    RationalDegree δ p i = TensorProduct ℤ (degree δ p i) ℚ := sorry

/-- The completed rational nonnegative Chow-cohomology carrier. -/
abbrev RationalCompletion : Type (u + 1) :=
  ∀ i : ℕ, RationalDegree δ p i

/-- `RationalCompletion` is the dependent product of all rationalized degrees. -/
theorem rationalCompletion_def :
    RationalCompletion δ p = (∀ i : ℕ, RationalDegree δ p i) := sorry

namespace RationalCompletion

/-- Two completed rational classes are equal when all coefficients agree. -/
@[ext]
theorem ext {a b : RationalCompletion δ p} (h : ∀ i, a i = b i) : a = b := sorry

/-- Transport a rational homogeneous class along an equality of degrees. -/
def castDegree {i j : ℕ} (h : i = j) (x : RationalDegree δ p i) :
    RationalDegree δ p j :=
  Eq.mp (congrArg (RationalDegree δ p) h) x

/-- Transport along reflexivity leaves a rational homogeneous class unchanged. -/
theorem castDegree_rfl {i : ℕ} (x : RationalDegree δ p i) :
    castDegree δ p rfl x = x := sorry

/-- Rational homogeneous multiplication, obtained by multiplying the homogeneous
embeddings in the rationalized total Chow ring and projecting to degree `i + j`. -/
def homogeneousMul {i j : ℕ} (x : RationalDegree δ p i) (y : RationalDegree δ p j) :
    RationalDegree δ p (i + j) :=
  TensorProduct.map
      (DirectSum.component ℤ ℕ (degree δ p) (i + j))
      (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
    (rationalHomogeneous δ p i x * rationalHomogeneous δ p j y)

/-- Rational homogeneous multiplication has the expected value on pure tensors. -/
theorem homogeneousMul_tmul {i j : ℕ} (a : degree δ p i) (b : degree δ p j)
    (q r : ℚ) :
    homogeneousMul δ p (a ⊗ₜ[ℤ] q) (b ⊗ₜ[ℤ] r) =
      Nonnegative.mul δ p a b ⊗ₜ[ℤ] (q * r) := sorry

/-- The convolution unit is the rationalized degree-zero identity class. -/
def one : RationalCompletion δ p
  | 0 => ChowCohomology.one δ p ⊗ₜ[ℤ] (1 : ℚ)
  | _ + 1 => 0

/-- The degree-zero coefficient of the convolution unit. -/
theorem one_apply_zero : one δ p 0 = ChowCohomology.one δ p ⊗ₜ[ℤ] (1 : ℚ) := sorry

/-- Every positive-degree coefficient of the convolution unit vanishes. -/
theorem one_apply_succ (n : ℕ) : one δ p (n + 1) = 0 := sorry

/-- The homogeneous product indexed by an antidiagonal element, transported to its
specified total degree. -/
def antidiagonalMul (a b : RationalCompletion δ p) (n : ℕ)
    (ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n}) : RationalDegree δ p n :=
  castDegree δ p (Finset.mem_antidiagonal.mp ij.property)
    (homogeneousMul δ p (a ij.1.1) (b ij.1.2))

/-- Finite Cauchy convolution on completed rational Chow-cohomology classes. -/
def mul (a b : RationalCompletion δ p) : RationalCompletion δ p :=
  fun n ↦ (Finset.antidiagonal n).attach.sum (antidiagonalMul δ p a b n)

/-- Multiplication is coefficientwise finite Cauchy convolution. -/
theorem mul_apply (a b : RationalCompletion δ p) (n : ℕ) :
    mul δ p a b n =
      (Finset.antidiagonal n).attach.sum (antidiagonalMul δ p a b n) := sorry

/-- The canonical unit on the rational completed nonnegative Chow ring. -/
noncomputable instance instOne : One (RationalCompletion δ p) := ⟨one δ p⟩

/-- The canonical convolution multiplication on the rational completed nonnegative Chow ring. -/
noncomputable instance instMul : Mul (RationalCompletion δ p) := ⟨mul δ p⟩

/-- Convolution multiplication is associative. -/
theorem mul_assoc_axiom (a b c : RationalCompletion δ p) : a * b * c = a * (b * c) := sorry

/-- The degree-zero identity is a left unit for convolution. -/
theorem one_mul_axiom (a : RationalCompletion δ p) : 1 * a = a := sorry

/-- The degree-zero identity is a right unit for convolution. -/
theorem mul_one_axiom (a : RationalCompletion δ p) : a * 1 = a := sorry

/-- Convolution distributes over addition in the right variable. -/
theorem mul_add_axiom (a b c : RationalCompletion δ p) :
    a * (b + c) = a * b + a * c := sorry

/-- Convolution distributes over addition in the left variable. -/
theorem add_mul_axiom (a b c : RationalCompletion δ p) :
    (a + b) * c = a * c + b * c := sorry

/-- The canonical ring structure on rational completed nonnegative Chow cohomology. -/
noncomputable instance instRing : Ring (RationalCompletion δ p) :=
  Ring.ofMinimalAxioms add_assoc zero_add neg_add_cancel
    (mul_assoc_axiom δ p) (one_mul_axiom δ p) (mul_one_axiom δ p)
      (mul_add_axiom δ p) (add_mul_axiom δ p)

end RationalCompletion

end AlgebraicGeometry.ChowCohomology.Nonnegative
