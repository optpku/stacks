/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Torsion.Basic
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Weakly associated primes in exact sequences

This module provides injective-map and exact-pair transport results for
`weaklyAssociatedPrimes`.
-/

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {M' : Type v} [AddCommGroup M'] [Module R M']
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {M'' : Type x} [AddCommGroup M''] [Module R M'']
variable {f : M' →ₗ[R] M} {g : M →ₗ[R] M''}

namespace weaklyAssociatedPrimes

/-- An injective linear map sends weakly associated primes into those of its
target. -/
@[stacks 0548 "injective transport"]
theorem subset_of_injective (hf : Function.Injective f) :
    weaklyAssociatedPrimes R M' ⊆ weaklyAssociatedPrimes R M := sorry

/-- In an exact pair `M' ⟶ M ⟶ M''`, every weakly associated prime of `M`
comes from `M'` or `M''`. -/
@[stacks 0548 "exact-sequence union"]
theorem subset_union_of_exact (hf : Function.Injective f) (hfg : Function.Exact f g) :
    weaklyAssociatedPrimes R M ⊆
      weaklyAssociatedPrimes R M' ∪ weaklyAssociatedPrimes R M'' := sorry

end weaklyAssociatedPrimes

end
