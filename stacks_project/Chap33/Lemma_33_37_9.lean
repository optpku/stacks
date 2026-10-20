/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.DimensionOne.MinimalPrime
import StacksCheckRecall

universe u

/- Lemma 33.37.9: In a Noetherian one-dimensional local ring, two maximal-ideal
elements with the same image in the product of minimal-prime localizations have
equal positive powers.
-/
@[stacks 0AB2] #check
  (IsLocalRing.DimensionOne.MinimalPrime.exists_pow_eq_of_equal_localizations :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      ringKrullDim R = 1 →
      ∀ {a₁ a₂ : R},
        a₁ ∈ IsLocalRing.maximalIdeal R →
        a₂ ∈ IsLocalRing.maximalIdeal R →
        algebraMap R (IsLocalRing.DimensionOne.MinimalPrime.localizations R) a₁ =
            algebraMap R (IsLocalRing.DimensionOne.MinimalPrime.localizations R) a₂ →
          ∃ n : ℕ, 0 < n ∧ a₁ ^ n = a₂ ^ n)
