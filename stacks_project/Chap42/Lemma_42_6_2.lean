/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.TameSymbol.TotalFractionRing.Reciprocity
import StacksCheckRecall

@[expose] public section

open scoped BigOperators nonZeroDivisors

universe u

/- Lemma 42.6.2: for two nonzerodivisors in a two-dimensional Noetherian local ring,
the sum over height-one primes of the orders of their local integral tame symbols is zero. -/
@[stacks 0EAW] #check (TameSymbol.Total.finsum_orderAt_eq_zero :
  (A : Type u) → [CommRing A] → [IsLocalRing A] → [IsNoetherianRing A] →
    (hdim : ringKrullDim A = 2) → (a b : A⁰) →
      ∑ᶠ p : PrimeSpectrum.HeightOne A,
        TameSymbol.Total.orderAt A hdim p a b = 0)
