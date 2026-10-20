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
# Prime Divided-Power Maps

This module contains the ideal-valued prime divided-power map and its elementary source
characterization. The uniqueness and existence statements live in Prime/Characterization.
-/

open scoped BigOperators
open Nat Ring

namespace DividedPowers

variable {A : Type*} [CommRing A] {I : Ideal A}

/-- The pth divided-power map of a divided power structure, viewed as an endomorphism of its
ideal. -/
@[stacks 07GS "prime divided-power map"]
abbrev dpowPrime (γ : DividedPowers I) (p : ℕ) [Fact p.Prime] : I → I :=
  fun x ↦ ⟨γ.dpow p x, γ.dpow_mem (Fact.out : p.Prime).ne_zero x.2⟩

/-- Coercing the ideal-valued prime divided-power map recovers the ambient divided power. -/
@[simp]
theorem coe_dpowPrime_apply (γ : DividedPowers I) (p : ℕ) [Fact p.Prime] (x : I) :
    (γ.dpowPrime p x : A) = γ.dpow p x := sorry

/-- The correction term in the additivity identity for a candidate prime divided-power map. -/
noncomputable def dpowPrimeAddCorrection (p : ℕ) (x y : I) : A :=
  Finset.sum (Finset.antidiagonal p) fun ij ↦
    if 0 < ij.1 ∧ 0 < ij.2 then
      inverse (ij.1.factorial : A) * inverse (ij.2.factorial : A) *
        (x : A) ^ ij.1 * (y : A) ^ ij.2
    else
      0

end DividedPowers

namespace Function

open DividedPowers

variable {A : Type*} [CommRing A] {I : Ideal A}

/-- The factorial, scalar-compatibility, and additivity identities for a candidate pth
divided-power map on an ideal. -/
@[stacks 07GS "prime divided-power identities"]
structure IsDpowPrime (δ : I → I) (p : ℕ) : Prop where
  /-- The factorial identity. -/
  factorial : ∀ x : I, ((p ! : A) * (δ x : A)) = (x : A) ^ p
  /-- Compatibility with scalar multiplication. -/
  smul : ∀ (a : A) (x : I), δ (a • x) = a ^ p • δ x
  /-- The additivity identity. -/
  add : ∀ x y : I,
    (δ (x + y) : A) = (δ x : A) + dpowPrimeAddCorrection p x y + δ y

/-- The expansion of Function.IsDpowPrime into its three defining identities. -/
theorem isDpowPrime_iff (δ : I → I) (p : ℕ) :
    δ.IsDpowPrime p ↔
      (∀ x : I, ((p ! : A) * (δ x : A)) = (x : A) ^ p) ∧
        (∀ (a : A) (x : I), δ (a • x) = a ^ p • δ x) ∧
          ∀ x y : I,
            (δ (x + y) : A) = (δ x : A) + dpowPrimeAddCorrection p x y + δ y := sorry

end Function

namespace DividedPowers

open Function

variable {A : Type*} [CommRing A] {I : Ideal A}

/-- The prime divided-power map of a divided power structure satisfies the three prime
divided-power identities under the prime-to-p unit hypothesis. -/
theorem isDpowPrime_dpowPrime (γ : DividedPowers I) (p : ℕ) [Fact p.Prime]
    (hunit : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) :
    (γ.dpowPrime p).IsDpowPrime p := sorry

end DividedPowers
