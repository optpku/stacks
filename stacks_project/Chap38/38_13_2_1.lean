/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.Ideal.AssociatedPrime.Restriction.Avoidance

universe u v w x

/- 38.13.2.1: an exact associated prime upstairs that lies over `p` contracts
to an exact associated prime controlled by the chosen localization element, so `p ≤ q`. -/
@[stacks 0CU7] #check (associatedPrimesOfModule.Restriction.le_of_liesOver_of_isUnit :
  ∀ {A : Type u} {B : Type v} {M : Type w} {M' : Type x}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module B M']
    (g : A) (q p : Ideal A) (P : Ideal B) [P.LiesOver p],
    IsUnit (algebraMap A B g) →
    (∀ Q ∈ associatedPrimesOfModule B M',
      Q.under A ∈ associatedPrimesOfModule A M) →
    (∀ r ∈ associatedPrimesOfModule A M, g ∉ r → r ≤ q) →
    P ∈ associatedPrimesOfModule B M' → p ≤ q)
