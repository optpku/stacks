module

import StacksCheckRecall
public import ReasLib.RingTheory.LocalRing.DimensionOne.PowerFactorization

universe u v

/- Lemma 42.4.3: for nonzerodivisors `a` and `b` in a one-dimensional Noetherian
local ring, with `a` in the maximal ideal, the exponent in any factorization of `b`
by a power of `a` in a finite injective ring extension is uniformly bounded. -/
@[stacks 0EAF] #check
  (IsLocalRing.DimensionOne.existsPowerFactorizationBound :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      ringKrullDim R = 1 → ∀ a b : R,
        a ∈ nonZeroDivisors R → b ∈ nonZeroDivisors R →
          a ∈ IsLocalRing.maximalIdeal R →
            ∃ n : ℕ, ∀ {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S],
              Function.Injective (algebraMap R S) → ∀ m : ℕ,
                (algebraMap R S a) ^ m ∣ algebraMap R S b → m ≤ n)
