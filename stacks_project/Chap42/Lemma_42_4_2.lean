/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.LocalRing.DimensionOne.CommonFactor

universe u

/-
Lemma 42.4.2: two nonzerodivisors in a one-dimensional Noetherian local ring acquire
a common nonzerodivisor factor in a finite injective extension whose cokernel is annihilated
by a power of the maximal ideal, and the residual factors generate the unit ideal.
-/
@[stacks 02Q7] #check
  (IsLocalRing.DimensionOne.exists_finiteExtension_commonFactor :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      ringKrullDim R = 1 → ∀ (a b : R),
        a ∈ nonZeroDivisors R → b ∈ nonZeroDivisors R →
          ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Module.Finite R S),
            Function.Injective (algebraMap R S) ∧
              Module.IsAnnihilatedByPower (IsLocalRing.maximalIdeal R)
                (S ⧸ (Algebra.linearMap R S).range) ∧
              ∃ t a' b' : S,
                t ∈ nonZeroDivisors S ∧ a' ∈ nonZeroDivisors S ∧
                  b' ∈ nonZeroDivisors S ∧
                  algebraMap R S a = t * a' ∧ algebraMap R S b = t * b' ∧
                    Ideal.span ({a', b'} : Set S) = ⊤)
