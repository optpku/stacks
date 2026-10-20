/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.DimensionOne.MinimalPrime
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 33.37.10

The minimal-prime-intersection power statement is the direct
`IsLocalRing.DimensionOne.MinimalPrime.exists_pow_mem_range_of_maximalIdeal_add_intersection`
API.
-/

universe u

/- Lemma 33.37.10: a maximal-ideal element plus an element of the extended intersection of the
minimal primes has a positive power in the image of the ring in the product of its
minimal-prime localizations. -/
@[stacks 0AB3] #check
  (IsLocalRing.DimensionOne.MinimalPrime.exists_pow_mem_range_of_maximalIdeal_add_intersection :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      ringKrullDim R = 1 →
        ∀ {a : R} {i f : IsLocalRing.DimensionOne.MinimalPrime.localizations R},
          a ∈ IsLocalRing.maximalIdeal R →
          i ∈ Ideal.map
            (algebraMap R (IsLocalRing.DimensionOne.MinimalPrime.localizations R))
            (nilradical R) →
          f = i + algebraMap R (IsLocalRing.DimensionOne.MinimalPrime.localizations R) a →
          ∃ n : ℕ, 0 < n ∧
            f ^ n ∈
              (algebraMap R (IsLocalRing.DimensionOne.MinimalPrime.localizations R)).range)
