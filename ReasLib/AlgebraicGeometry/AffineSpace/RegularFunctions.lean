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
public import Mathlib.FieldTheory.Finite.Polynomial
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
  Iff.rfl

/-- The difference of nested zero loci is Zariski locally closed. -/
theorem isZariskiLocallyClosed_sdiff {I J : Ideal (MvPolynomial σ k)} (hIJ : I ≤ J) :
    IsZariskiLocallyClosed (zeroLocus k I \ zeroLocus k J) :=
  ⟨I, J, hIJ, rfl⟩

/-- Affine space is Zariski locally closed in itself. -/
theorem isZariskiLocallyClosed_univ :
    IsZariskiLocallyClosed (Set.univ : Set (σ → k)) :=
  by
    refine ⟨(⊥ : Ideal (MvPolynomial σ k)), ⊤, bot_le, ?_⟩
    simp

/-- A relative Zariski open of `Z` is the complement in `Z` of a zero locus. -/
def IsZariskiOpenIn (U Z : Set (σ → k)) : Prop :=
  U ⊆ Z ∧ ∃ I : Ideal (MvPolynomial σ k), U = Z \ zeroLocus k I

/-- Relative Zariski opens are complements of zero loci inside `Z`. -/
theorem isZariskiOpenIn_iff (U Z : Set (σ → k)) :
    IsZariskiOpenIn U Z ↔
      U ⊆ Z ∧ ∃ I : Ideal (MvPolynomial σ k), U = Z \ zeroLocus k I :=
  Iff.rfl

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
  Iff.rfl

/-- A function on a subset of affine space is polynomial if it is given by evaluation of a
polynomial. -/
def IsPolynomial {Z : Set (σ → k)} (φ : Z → k) : Prop :=
  ∃ p : MvPolynomial σ k, ∀ z : Z, φ z = eval z.val p

/-- Polynomial functions are those given by evaluation of a polynomial. -/
theorem isPolynomial_iff {Z : Set (σ → k)} (φ : Z → k) :
    IsPolynomial φ ↔ ∃ p : MvPolynomial σ k, ∀ z : Z, φ z = eval z.val p :=
  Iff.rfl

private theorem zeroLocus_mul_eq_union {I J : Ideal (MvPolynomial σ k)} :
    zeroLocus k (I * J) = zeroLocus k I ∪ zeroLocus k J := by
  ext x
  constructor
  · intro hx
    by_cases hxI : x ∈ zeroLocus k I
    · exact Set.mem_union_left _ hxI
    · by_cases hxJ : x ∈ zeroLocus k J
      · exact Set.mem_union_right _ hxJ
      · exfalso
        simp only [mem_zeroLocus_iff, not_forall] at hxI hxJ
        obtain ⟨pI, hpI, hpI0⟩ := hxI
        obtain ⟨pJ, hpJ, hpJ0⟩ := hxJ
        have hprod := hx (pI * pJ) (Ideal.mul_mem_mul hpI hpJ)
        simp only [map_mul] at hprod
        exact (mul_ne_zero hpI0 hpJ0) hprod
  · rintro (hxI | hxJ)
    · exact zeroLocus_anti_mono (K := k) Ideal.mul_le_right hxI
    · exact zeroLocus_anti_mono (K := k) Ideal.mul_le_left hxJ

/-- Polynomial functions are regular. -/
theorem isRegular_of_isPolynomial {Z : Set (σ → k)} {φ : Z → k}
    (hφ : IsPolynomial φ) : IsRegular φ :=
  by
    rcases hφ with ⟨p, hp⟩
    intro z
    refine ⟨Z, ?_, z.property, p, 1, ?_, ?_⟩
    · refine ⟨Set.Subset.rfl, ?_⟩
      refine ⟨⊤, ?_⟩
      simp
    · intro u hu
      simp
    · intro u hu
      simpa using hp u

/-- Regular functions are closed under pointwise addition. -/
theorem isRegular_add {Z : Set (σ → k)} {φ ψ : Z → k}
    (hφ : IsRegular φ) (hψ : IsRegular ψ) : IsRegular (φ + ψ) :=
  by
    intro z
    rcases hφ z with ⟨U, hU, hzU, f, g, hg, hf⟩
    rcases hψ z with ⟨V, hV, hzV, f', g', hg', hf'⟩
    rcases hU with ⟨hUZ, ⟨I, hUI⟩⟩
    rcases hV with ⟨hVZ, ⟨J, hVJ⟩⟩
    refine ⟨U ∩ V, ?_, ⟨hzU, hzV⟩, f * g' + f' * g, g * g', ?_, ?_⟩
    · refine ⟨fun x hx ↦ hUZ hx.1, ?_⟩
      refine ⟨I * J, ?_⟩
      rw [hUI, hVJ, zeroLocus_mul_eq_union]
      ext x
      simp [and_assoc, and_left_comm, and_comm]
    · intro u hu
      simp only [map_mul]
      exact mul_ne_zero (hg u hu.1) (hg' u hu.2)
    · intro u hu
      change φ u + ψ u = _
      rw [hf u hu.1, hf' u hu.2]
      simp only [map_add, map_mul]
      field_simp [hg u hu.1, hg' u hu.2]

/-- Regular functions are closed under pointwise multiplication. -/
theorem isRegular_mul {Z : Set (σ → k)} {φ ψ : Z → k}
    (hφ : IsRegular φ) (hψ : IsRegular ψ) : IsRegular (φ * ψ) :=
  by
    intro z
    rcases hφ z with ⟨U, hU, hzU, f, g, hg, hf⟩
    rcases hψ z with ⟨V, hV, hzV, f', g', hg', hf'⟩
    rcases hU with ⟨hUZ, ⟨I, hUI⟩⟩
    rcases hV with ⟨hVZ, ⟨J, hVJ⟩⟩
    refine ⟨U ∩ V, ?_, ⟨hzU, hzV⟩, f * f', g * g', ?_, ?_⟩
    · refine ⟨fun x hx ↦ hUZ hx.1, ?_⟩
      refine ⟨I * J, ?_⟩
      rw [hUI, hVJ, zeroLocus_mul_eq_union]
      ext x
      simp [and_assoc, and_left_comm, and_comm]
    · intro u hu
      simp only [map_mul]
      exact mul_ne_zero (hg u hu.1) (hg' u hu.2)
    · intro u hu
      change φ u * ψ u = _
      rw [hf u hu.1, hf' u hu.2]
      simp only [map_mul]
      field_simp [hg u hu.1, hg' u hu.2]

/-- Constant functions on affine space are regular. -/
theorem isRegular_const {Z : Set (σ → k)} (c : k) :
    IsRegular (algebraMap k (Z → k) c) :=
  by
    intro z
    refine ⟨Z, ?_, z.property, MvPolynomial.C c, 1, ?_, ?_⟩
    · refine ⟨Set.Subset.rfl, ?_⟩
      refine ⟨⊤, ?_⟩
      simp
    · intro u hu
      simp
    · intro u hu
      simp

/-- The algebra of regular functions on a subset of affine space. -/
def regularFunctions (Z : Set (σ → k)) : Subalgebra k (Z → k) where
  carrier := {φ | IsRegular φ}
  add_mem' := isRegular_add
  mul_mem' := isRegular_mul
  algebraMap_mem' := isRegular_const

/-- Membership in `regularFunctions Z` is regularity. -/
theorem mem_regularFunctions_iff {Z : Set (σ → k)} {φ : Z → k} :
    φ ∈ regularFunctions Z ↔ IsRegular φ :=
  Iff.rfl

/-- The identification of a scalar with a point of the affine line. -/
def affineLinePoint (x : k) : Fin 1 → k := fun _ ↦ x

/-- Evaluating `affineLinePoint x` at the unique index recovers `x`. -/
theorem affineLinePoint_apply (x : k) (i : Fin 1) : affineLinePoint x i = x :=
  rfl

/-- Over an algebraically closed field, every regular function on affine space is polynomial. -/
theorem isPolynomial_of_isRegular_univ {k : Type u} [Field k] [IsAlgClosed k]
    {n : ℕ} (φ : ∀ (x : (Set.univ : Set (Fin n → k))), k) (hφ : IsRegular φ) :
    IsPolynomial φ :=
  sorry

/-- Every function on a locally closed affine subset over a finite field is regular. -/
theorem isRegular_of_finite {k : Type u} [Field k] [Finite k] {n : ℕ}
    {Z : Set (Fin n → k)} (hZ : IsZariskiLocallyClosed Z) (φ : Z → k) :
    IsRegular φ :=
  by
    classical
    letI : Fintype k := Fintype.ofFinite k
    let e : (Fin n → k) → k := fun x ↦ if hx : x ∈ Z then φ ⟨x, hx⟩ else 0
    let p : MvPolynomial (Fin n) k := ∑ a : Fin n → k, C (e a) * indicator a
    apply isRegular_of_isPolynomial
    refine ⟨p, ?_⟩
    intro z
    change φ z = eval z.val (∑ a : Fin n → k, C (e a) * indicator a)
    rw [map_sum, Finset.sum_eq_single z.val]
    · simp [e, z.property, eval_indicator_apply_eq_one]
    · intro b hb hne
      simp only [map_mul]
      rw [eval_indicator_apply_eq_zero _ _ (Ne.symm hne), mul_zero]
    · intro hz
      exact (hz (Finset.mem_univ _)).elim

/-- Over a finite field, regular functions on a locally closed affine subset form a finite-dimensional
algebra. -/
theorem finiteDimensional_regularFunctions {k : Type u} [Field k] [Finite k]
    {n : ℕ} {Z : Set (Fin n → k)} (hZ : IsZariskiLocallyClosed Z) :
    FiniteDimensional k (regularFunctions Z) :=
  by
    letI : Fintype k := Fintype.ofFinite k
    letI : Finite Z := inferInstance
    exact FiniteDimensional.finiteDimensional_subalgebra (regularFunctions Z)

end MvPolynomial
