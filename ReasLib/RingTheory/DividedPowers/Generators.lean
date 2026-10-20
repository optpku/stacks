/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Divided Powers from Generators

This module packages the generator-level divided-power identities and their existence and
uniqueness consequence.
-/

universe u

open Finset

namespace DividedPowers

variable {A : Type u} [CommSemiring A]

/-- The divided-power identities required on a generating set of an ideal. -/
@[stacks 07GP "divided-power axioms on generators"]
structure AxiomsOnGenerators (I : Ideal A) (γ : ℕ → A → A) (S : Set A) : Prop where
  /-- The specified set generates the ideal. -/
  span : I = Ideal.span S
  /-- The zeroth operation is one on the ideal. -/
  zero : ∀ ⦃x : A⦄, x ∈ I → γ 0 x = 1
  /-- The first operation is the identity on the ideal. -/
  one : ∀ ⦃x : A⦄, x ∈ I → γ 1 x = x
  /-- Positive operations preserve the ideal. -/
  mem : ∀ ⦃n : ℕ⦄ ⦃x : A⦄, n ≠ 0 → x ∈ I → γ n x ∈ I
  /-- The addition formula holds on the ideal. -/
  add : ∀ ⦃n : ℕ⦄ ⦃x y : A⦄, x ∈ I → y ∈ I →
    γ n (x + y) = (antidiagonal n).sum fun k ↦ γ k.1 x * γ k.2 y
  /-- The scalar formula holds on the ideal. -/
  mul : ∀ ⦃n : ℕ⦄ ⦃a x : A⦄, x ∈ I → γ n (a * x) = a ^ n * γ n x
  /-- The multiplicative divided-power identity holds on the chosen generators. -/
  mul_dpow_gen : ∀ ⦃m n : ℕ⦄ ⦃x : A⦄, m ≠ 0 → x ∈ S →
    γ m x * γ n x = Nat.choose (m + n) m * γ (m + n) x
  /-- The iterated divided-power identity holds on the chosen generators. -/
  comp_gen : ∀ ⦃m n : ℕ⦄ ⦃x : A⦄, n ≠ 0 → x ∈ S →
    γ m (γ n x) = Nat.uniformBell m n * γ (m * n) x

namespace AxiomsOnGenerators

variable {I : Ideal A} {γ : ℕ → A → A} {S : Set A}

/-- Extend the prescribed operations by zero away from the ideal on which they define divided
powers. -/
noncomputable def candidateDpow (I : Ideal A) (γ : ℕ → A → A) : ℕ → A → A :=
  open scoped Classical in fun n x ↦ if x ∈ I then γ n x else 0

/-- The extended candidate operation vanishes away from its ideal. -/
theorem candidateDpow_null (I : Ideal A) (γ : ℕ → A → A) {n : ℕ} {x : A}
    (hx : x ∉ I) : candidateDpow I γ n x = 0 := sorry

/-- On the ideal, the zeroth candidate operation is one. -/
theorem candidateDpow_zero (hγ : AxiomsOnGenerators I γ S) {x : A}
    (hx : x ∈ I) : candidateDpow I γ 0 x = 1 := sorry

/-- On the ideal, the first candidate operation is the identity. -/
theorem candidateDpow_one (hγ : AxiomsOnGenerators I γ S) {x : A}
    (hx : x ∈ I) : candidateDpow I γ 1 x = x := sorry

/-- Positive candidate operations preserve the ideal. -/
theorem candidateDpow_mem (hγ : AxiomsOnGenerators I γ S) {n : ℕ} {x : A}
    (hn : n ≠ 0) (hx : x ∈ I) : candidateDpow I γ n x ∈ I := sorry

/-- The candidate operations satisfy the divided-power addition identity. -/
theorem candidateDpow_add (hγ : AxiomsOnGenerators I γ S) {n : ℕ} {x y : A}
    (hx : x ∈ I) (hy : y ∈ I) :
    candidateDpow I γ n (x + y) =
      (antidiagonal n).sum fun k ↦ candidateDpow I γ k.1 x * candidateDpow I γ k.2 y := sorry

/-- The candidate operations satisfy the divided-power scalar identity. -/
theorem candidateDpow_mul (hγ : AxiomsOnGenerators I γ S) {n : ℕ} {a x : A}
    (hx : x ∈ I) :
    candidateDpow I γ n (a * x) = a ^ n * candidateDpow I γ n x := sorry

/-- The candidate operations satisfy the divided-power multiplication identity. -/
theorem candidateDpow_mul_dpow (hγ : AxiomsOnGenerators I γ S)
    {m n : ℕ} {x : A} (hx : x ∈ I) :
    candidateDpow I γ m x * candidateDpow I γ n x =
      Nat.choose (m + n) m * candidateDpow I γ (m + n) x := sorry

/-- The candidate operations satisfy the iterated divided-power identity. -/
theorem candidateDpow_comp (hγ : AxiomsOnGenerators I γ S)
    {m n : ℕ} {x : A} (hn : n ≠ 0) (hx : x ∈ I) :
    candidateDpow I γ m (candidateDpow I γ n x) =
      Nat.uniformBell m n * candidateDpow I γ (m * n) x := sorry

/-- The canonical divided-power structure assembled from operations satisfying the identities on
a generating set.  Away from the generated ideal, its operations are extended by zero. -/
@[stacks 07GP "canonical divided powers from generators"]
noncomputable def dividedPowers (hγ : AxiomsOnGenerators I γ S) : DividedPowers I where
  dpow := candidateDpow I γ
  dpow_null := candidateDpow_null I γ
  dpow_zero := candidateDpow_zero hγ
  dpow_one := candidateDpow_one hγ
  dpow_mem := candidateDpow_mem hγ
  dpow_add := candidateDpow_add hγ
  dpow_mul := candidateDpow_mul hγ
  mul_dpow := candidateDpow_mul_dpow hγ
  dpow_comp := candidateDpow_comp hγ

/-- On the generated ideal, the canonical divided-power structure is the prescribed operation. -/
@[simp]
theorem dividedPowers_dpow (hγ : AxiomsOnGenerators I γ S) {n : ℕ} {x : A}
    (hx : x ∈ I) : hγ.dividedPowers.dpow n x = γ n x := sorry

/-- A divided-power structure with the prescribed operations is the canonical structure assembled
from the generator-level axioms. -/
theorem eq_dividedPowers_of_dpow_eq (hγ : AxiomsOnGenerators I γ S)
    (hI : DividedPowers I)
    (h : ∀ ⦃n : ℕ⦄ ⦃x : A⦄, x ∈ I → hI.dpow n x = γ n x) :
    hI = hγ.dividedPowers := sorry

/-- Generator-level divided-power axioms produce a divided power structure with the prescribed
operations on the ideal. -/
theorem exists_dividedPowers (hγ : AxiomsOnGenerators I γ S) :
    ∃ hI : DividedPowers I, ∀ ⦃n : ℕ⦄ ⦃x : A⦄, x ∈ I → hI.dpow n x = γ n x := sorry

/-- Lemma 23.2.4 (Tag 07GP): generator-level divided-power axioms produce a unique divided power
structure with the prescribed operations on the ideal. -/
@[stacks 07GP]
theorem existsUnique_dividedPowers (hγ : AxiomsOnGenerators I γ S) :
    ∃! hI : DividedPowers I, ∀ ⦃n : ℕ⦄ ⦃x : A⦄, x ∈ I → hI.dpow n x = γ n x := sorry

end AxiomsOnGenerators

end DividedPowers
