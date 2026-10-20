/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Finsupp.Basic
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.ExactSequence
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Weakly associated primes of direct sums

The tensor-product proof of scalar-extension statements repeatedly reduces to
finitely supported families of a module.  These two inclusions expose that
reduction at the owner level, without committing consumers to a chosen basis
or to a recursive proof over `Option`.
-/

universe u v

section

variable {R : Type u} [CommRing R]

namespace weaklyAssociatedPrimes

/-- Weakly associated primes of a binary product come from one of its factors. -/
@[stacks 0CUB "binary direct-sum decomposition"]
theorem prod {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] :
    weaklyAssociatedPrimes R (M₁ × M₂) =
      weaklyAssociatedPrimes R M₁ ∪ weaklyAssociatedPrimes R M₂ := sorry

/-- The finite-support reduction remains valid for an arbitrary index type,
because every witness has finite support. -/
@[stacks 0CUB "direct-sum descent"]
theorem subset_of_finsupp {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} :
    weaklyAssociatedPrimes R (ι →₀ M) ⊆ weaklyAssociatedPrimes R M := sorry

end weaklyAssociatedPrimes

end
