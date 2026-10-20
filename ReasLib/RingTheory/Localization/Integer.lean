/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.Integer

/-!
# Clearing denominators in ring extensions

This module records a simultaneous numerator and denominator form for a localized element whose
prescribed coefficient-weighted powers come from the base localization.
-/

@[expose] public section

universe u

namespace IsLocalization

/-- Let `A → B` be an injective map of commutative rings, and localize both rings at a
submonoid `S ⊆ A`. If `x` does not come from the localization of `A`, but every
`b i * x ^ (i + 1)` does, then `x` has a common denominator `s ∈ S` and a numerator `y ∈ B`
which does not come from `A`, while every `b i * y ^ (i + 1)` does come from `A`. -/
theorem exists_numerator_not_isInteger_of_mul_pow_isInteger
    {A B Aₛ Bₛ : Type u} [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₛ]
    [Algebra A B] [FaithfulSMul A B] {S : Submonoid A}
    [Algebra A Aₛ] [IsLocalization S Aₛ]
    [Algebra B Bₛ] [IsLocalization (Algebra.algebraMapSubmonoid B S) Bₛ]
    [Algebra A Bₛ] [Algebra Aₛ Bₛ]
    [IsScalarTower A B Bₛ] [IsScalarTower A Aₛ Bₛ]
    {n : ℕ} (hn : 0 < n) (b : Fin n → B) (x : Bₛ)
    (hx : ¬ IsInteger Aₛ x)
    (hbx : ∀ i, IsInteger Aₛ (algebraMap B Bₛ (b i) * x ^ ((i : ℕ) + 1))) :
    ∃ (s : S) (y : B),
      algebraMap B Bₛ y = algebraMap A Bₛ s * x ∧
        ¬ IsInteger A y ∧
          ∀ i, IsInteger A (b i * y ^ ((i : ℕ) + 1)) := sorry

end IsLocalization
