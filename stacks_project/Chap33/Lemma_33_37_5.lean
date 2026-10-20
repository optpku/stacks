/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall

public import ReasLib.RingTheory.Localization.FractionRing.IntegralClosure

@[expose] public section

universe u

#check (@FractionRing.IntegralClosure.isDedekind_of_dim_one :
  ∀ {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Finite (MaximalSpectrum B)],
    ringKrullDim B = 1 → IsDedekindDomain (integralClosure B (FractionRing B)))

#check (@FractionRing.IntegralClosure.finiteMaximalSpectrum_of_dim_one :
  ∀ {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Finite (MaximalSpectrum B)],
    ringKrullDim B = 1 → Finite (MaximalSpectrum (integralClosure B (FractionRing B))))

/- Lemma 33.37.5: a nonzero element of the Jacobson radical of the integral
closure clears every element back into the base ring after multiplication by
a suitable power. -/
@[stacks 09N2] #check
  (@FractionRing.IntegralClosure.exists_pow_mul_mem_base_of_mem_jacobson :
    ∀ {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B]
      [Finite (MaximalSpectrum B)],
      ringKrullDim B = 1 → ∀ x y : integralClosure B (FractionRing B),
        x ∈ Ring.jacobson (integralClosure B (FractionRing B)) → x ≠ 0 →
          ∃ n : ℕ, ∃ b : B,
            algebraMap B (integralClosure B (FractionRing B)) b = x ^ n * y)
