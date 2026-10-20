/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.DividedPowers.Prime.Basic

@[expose] public section

open Nat Ring

/-!
# Characterizing Divided Powers by a Prime Operation

This module gives the prime-to-p uniqueness and existence API for divided power structures.
-/

namespace Ideal

open DividedPowers Function

variable {A : Type*} [CommRing A]

/-- Lemma 23.5.3 (1) (Tag 07GS): under the prime-to-p unit hypothesis, a divided power
structure is determined by its ideal-valued pth divided-power map. -/
@[stacks 07GS "(1)"]
theorem dividedPowers_eq_iff_dpowPrime_eq (p : ℕ) [Fact p.Prime] (I : Ideal A)
    (hunit : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) {γ γ' : DividedPowers I} :
    γ = γ' ↔ γ.dpowPrime p = γ'.dpowPrime p := sorry

/-- Under the prime-to-p unit hypothesis, the prime divided-power map is injective. -/
theorem injective_dpowPrime (p : ℕ) [Fact p.Prime] (I : Ideal A)
    (hunit : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) :
    Function.Injective fun γ : DividedPowers I ↦ γ.dpowPrime p := sorry

/-- Pointwise form of the criterion that a prime divided-power map determines its divided
power structure. -/
theorem dividedPowers_eq_iff_forall_dpowPrime_eq (p : ℕ) [Fact p.Prime] (I : Ideal A)
    (hunit : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) {γ γ' : DividedPowers I} :
    γ = γ' ↔ ∀ x : I, γ.dpowPrime p x = γ'.dpowPrime p x := sorry

/-- Lemma 23.5.3 (2) (Tag 07GS): a map satisfying the three prime divided-power identities
extends uniquely to a divided power structure under the prime-to-p unit hypothesis. -/
@[stacks 07GS]
theorem existsUnique_dividedPowers_of_dpowPrime (p : ℕ) [Fact p.Prime] (I : Ideal A)
    (hunit : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    (hfactorial : ∀ x : I, ((p ! : A) * (δ x : A)) = (x : A) ^ p)
    (hsmul : ∀ (a : A) (x : I), δ (a • x) = a ^ p • δ x)
    (hadd : ∀ x y : I,
      (δ (x + y) : A) = (δ x : A) + dpowPrimeAddCorrection p x y + δ y) :
    ∃! γ : DividedPowers I, γ.dpowPrime p = δ := sorry

/-- Bundled form of the unique-extension criterion for a prime divided-power map. -/
theorem existsUnique_dividedPowers_of_isDpowPrime (p : ℕ) [Fact p.Prime] (I : Ideal A)
    (hunit : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    (hδ : δ.IsDpowPrime p) :
    ∃! γ : DividedPowers I, γ.dpowPrime p = δ := sorry

end Ideal

namespace Function.IsDpowPrime

open DividedPowers

variable {A : Type*} [CommRing A]
variable {p : ℕ} [Fact p.Prime]

/-- Remark 23.5.4 (Tag 0H87): under the prime-to-`p` unit hypothesis, scalar compatibility and
the divided-power addition formula force the factorial identity for a candidate `p`th divided
power operation. -/
@[stacks 0H87 "factorial identity"]
theorem factorial_of_smul_add (I : Ideal A)
    (hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A))
    (delta : I → I)
    (hsmul : ∀ (a : A) (x : I), delta (a • x) = a ^ p • delta x)
    (hadd : ∀ x y : I,
      (delta (x + y) : A) =
        (delta x : A) + dpowPrimeAddCorrection p x y + delta y)
    (x : I) :
    (p ! : A) * (delta x : A) = (x : A) ^ p := sorry

/-- Remark 23.5.4 (Tag 0H87): under the prime-to-`p` unit hypothesis, scalar compatibility and
the divided-power addition formula suffice to construct the bundled prime divided-power
predicate. -/
@[stacks 0H87 "constructor from scalar and addition laws"]
theorem of_smul_add (I : Ideal A)
    (hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A))
    (delta : I → I)
    (hsmul : ∀ (a : A) (x : I), delta (a • x) = a ^ p • delta x)
    (hadd : ∀ x y : I,
      (delta (x + y) : A) =
        (delta x : A) + dpowPrimeAddCorrection p x y + delta y) :
    delta.IsDpowPrime p := sorry

end Function.IsDpowPrime
