/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Nullstellensatz

/-!
# Classical regular functions on affine space

Regular functions on a Zariski locally closed subset of the k-points of affine space,
in the classical (not scheme-theoretic) sense.
-/

@[expose] public section

noncomputable section

universe u v

namespace MvPolynomial

variable {k : Type u} {σ : Type v} [Field k]

/-- A subset of affine space is Zariski locally closed when it is the difference of
zero loci of nested ideals. -/
def IsZariskiLocallyClosed (Z : Set (σ → k)) : Prop :=
  ∃ I J : Ideal (MvPolynomial σ k), I ≤ J ∧ Z = zeroLocus k I \ zeroLocus k J

/-- Zariski locally closed subsets are exactly differences of nested zero loci. -/
theorem isZariskiLocallyClosed_iff (Z : Set (σ → k)) :
    IsZariskiLocallyClosed Z ↔
      ∃ I J : Ideal (MvPolynomial σ k), I ≤ J ∧ Z = zeroLocus k I \ zeroLocus k J :=
  sorry

/-- The difference of nested zero loci is Zariski locally closed. -/
theorem isZariskiLocallyClosed_sdiff {I J : Ideal (MvPolynomial σ k)} (hIJ : I ≤ J) :
    IsZariskiLocallyClosed (zeroLocus k I \ zeroLocus k J) :=
  sorry

/-- Affine space is Zariski locally closed in itself. -/
theorem isZariskiLocallyClosed_univ :
    IsZariskiLocallyClosed (Set.univ : Set (σ → k)) :=
  sorry

/-- A relative Zariski open of `Z` is the complement in `Z` of a zero locus. -/
def IsZariskiOpenIn (U Z : Set (σ → k)) : Prop :=
  U ⊆ Z ∧ ∃ I : Ideal (MvPolynomial σ k), U = Z \ zeroLocus k I

/-- Relative Zariski opens are complements of zero loci inside `Z`. -/
theorem isZariskiOpenIn_iff (U Z : Set (σ → k)) :
    IsZariskiOpenIn U Z ↔
      U ⊆ Z ∧ ∃ I : Ideal (MvPolynomial σ k), U = Z \ zeroLocus k I :=
  sorry

/-- A function on a subset of affine space is regular if it is Zariski-locally a ratio of
polynomials with nonvanishing denominator. -/
def IsRegular {Z : Set (σ → k)} (φ : Z → k) : Prop :=
  ∀ z : Z, ∃ U : Set (σ → k), IsZariskiOpenIn U Z ∧ z.val ∈ U ∧
    ∃ f g : MvPolynomial σ k,
      (∀ u ∈ U, eval u g ≠ 0) ∧
      (∀ u : Z, u.val ∈ U → φ u = eval u.val f / eval u.val g)

/-- Regularity is the existence of local polynomial ratios with nonvanishing denominator. -/
theorem isRegular_iff {Z : Set (σ → k)} (φ : Z → k) :
    IsRegular φ ↔
      ∀ z : Z, ∃ U : Set (σ → k), IsZariskiOpenIn U Z ∧ z.val ∈ U ∧
        ∃ f g : MvPolynomial σ k,
          (∀ u ∈ U, eval u g ≠ 0) ∧
          (∀ u : Z, u.val ∈ U → φ u = eval u.val f / eval u.val g) :=
  sorry

/-- A function on a subset of affine space is polynomial if it is given by evaluation of a
polynomial. -/
def IsPolynomial {Z : Set (σ → k)} (φ : Z → k) : Prop :=
  ∃ p : MvPolynomial σ k, ∀ z : Z, φ z = eval z.val p

/-- Polynomial functions are those given by evaluation of a polynomial. -/
theorem isPolynomial_iff {Z : Set (σ → k)} (φ : Z → k) :
    IsPolynomial φ ↔ ∃ p : MvPolynomial σ k, ∀ z : Z, φ z = eval z.val p :=
  sorry

/-- Polynomial functions are regular. -/
theorem isRegular_of_isPolynomial {Z : Set (σ → k)} {φ : Z → k}
    (hφ : IsPolynomial φ) : IsRegular φ :=
  sorry

/-- Regular functions are closed under pointwise addition. -/
theorem isRegular_add {Z : Set (σ → k)} {φ ψ : Z → k}
    (hφ : IsRegular φ) (hψ : IsRegular ψ) : IsRegular (φ + ψ) :=
  sorry

/-- Regular functions are closed under pointwise multiplication. -/
theorem isRegular_mul {Z : Set (σ → k)} {φ ψ : Z → k}
    (hφ : IsRegular φ) (hψ : IsRegular ψ) : IsRegular (φ * ψ) :=
  sorry

/-- Constant functions on affine space are regular. -/
theorem isRegular_const {Z : Set (σ → k)} (c : k) :
    IsRegular (algebraMap k (Z → k) c) :=
  sorry

/-- The algebra of regular functions on a subset of affine space. -/
def regularFunctions (Z : Set (σ → k)) : Subalgebra k (Z → k) where
  carrier := {φ | IsRegular φ}
  add_mem' := isRegular_add
  mul_mem' := isRegular_mul
  algebraMap_mem' := isRegular_const

/-- Membership in `regularFunctions Z` is regularity. -/
theorem mem_regularFunctions_iff {Z : Set (σ → k)} {φ : Z → k} :
    φ ∈ regularFunctions Z ↔ IsRegular φ :=
  sorry

/-- The identification of a scalar with a point of the affine line. -/
def affineLinePoint (x : k) : Fin 1 → k := fun _ ↦ x

/-- Evaluating `affineLinePoint x` at the unique index recovers `x`. -/
theorem affineLinePoint_apply (x : k) (i : Fin 1) : affineLinePoint x i = x :=
  sorry

/-- Over an algebraically closed field, every regular function on affine space is polynomial. -/
theorem isPolynomial_of_isRegular_univ {k : Type u} [Field k] [IsAlgClosed k]
    {n : ℕ} (φ : ∀ (x : (Set.univ : Set (Fin n → k))), k) (hφ : IsRegular φ) :
    IsPolynomial φ :=
  sorry

/-- Every function on a locally closed affine subset over a finite field is regular. -/
theorem isRegular_of_finite {k : Type u} [Field k] [Finite k] {n : ℕ}
    {Z : Set (Fin n → k)} (hZ : IsZariskiLocallyClosed Z) (φ : Z → k) :
    IsRegular φ :=
  sorry

/-- Over a finite field, regular functions on a locally closed affine subset form a finite-dimensional
algebra. -/
theorem finiteDimensional_regularFunctions {k : Type u} [Field k] [Finite k]
    {n : ℕ} {Z : Set (Fin n → k)} (hZ : IsZariskiLocallyClosed Z) :
    FiniteDimensional k (regularFunctions Z) :=
  sorry

end MvPolynomial
