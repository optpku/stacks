/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import StacksCheckRecall

/-!
# Lifting minimal primes along injective maps

@stack 00FK
-/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.30.5: for an injective ring homomorphism `f : R →+* S`, every minimal prime ideal
of `R` is the contraction of a prime ideal of `S`. This is exactly the canonical owner theorem
`Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective` (Stacks tag `00FK`). -/
@[stacks 00FK]
#check @Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective
