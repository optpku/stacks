/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.DimensionOne.MinimalPrime
import StacksCheckRecall

/-!
# Lemma 33.37.11

The integral-source image and maximal-radical conclusion is the direct
`IsLocalRing.DimensionOne.MinimalPrime.exists_sameImage_integralSourceElem`
API.
-/

universe u v

#check @IsLocalRing.DimensionOne.MinimalPrime.localizations

/- Lemma 33.37.11: For a Noetherian local commutative ring `R` of Krull dimension one,
an integral ring homomorphism from a commutative ring `K` to the product of the
localizations of `R` at its minimal primes has an element with the same image as an element
`a` of the maximal ideal, where the radical of `(a)` is the maximal ideal. -/
@[stacks 0AB4] #check
  (IsLocalRing.DimensionOne.MinimalPrime.exists_sameImage_integralSourceElem :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      ringKrullDim R = 1 →
        ∀ {K : Type v} [CommRing K],
          (f : K →+* IsLocalRing.DimensionOne.MinimalPrime.localizations R) →
            f.IsIntegral →
              ∃ a : IsLocalRing.maximalIdeal R, ∃ x : K,
                algebraMap R (IsLocalRing.DimensionOne.MinimalPrime.localizations R) a = f x ∧
                  IsLocalRing.maximalIdeal R =
                    (Ideal.span ({(a : R)} : Set R)).radical)
