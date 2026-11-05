/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.Padic
import StacksCheckRecall

@[expose] public section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {A : Type u} [CommRing A]

/- Example 23.2.3 (07GN): prime-to-`p` integers being units suffices for the canonical
formula on `(p)`. The coefficient inverts only the prime-free part of the factorial. -/
@[stacks 07GN]
#check (PadicInt.existsUnique_primeLocalDividedPowers p A :
  (∀ k : ℕ, ¬ p ∣ k → IsUnit (k : A)) →
    ∃! gamma : DividedPowers (Ideal.span ({(p : A)} : Set A)),
      ∀ (n : ℕ) (a : A),
        gamma.dpow n ((p : A) * a) = PadicInt.primeLocalCoefficient p n A * a ^ n)

#check @PadicInt.primeLocalDividedPowers_dpow
#check @PadicInt.primeLocalCoefficient_eq_padic
#check @PadicInt.primeLocalDividedPowers_eq_algebraDividedPowers

-- Retain the p-adic specialization and its compatibility checks.
variable [Algebra ℤ_[p] A]

#check (PadicInt.existsUnique_dividedPowers_span_prime (p := p) (A := A) :
  ∃! gamma : DividedPowers (Ideal.span ({(p : A)} : Set A)),
    ∀ (n : ℕ) (a : A),
      gamma.dpow n ((p : A) * a) =
        algebraMap ℤ_[p] A ((PadicInt.dividedPowers p).dpow n (p : ℤ_[p])) * a ^ n)

#check @PadicInt.coe_dpow_eq_of_mem
#check @PadicInt.dividedPowers_extends_algebraMap
#check @PadicInt.isDPMorphism_iff_dpow_mul
#check @PadicInt.dividedPowers_eq_of_isDPMorphism
