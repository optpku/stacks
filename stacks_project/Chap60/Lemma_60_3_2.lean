/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.DividedPowers.BilinearExtension

@[expose] public section

universe u v w

/- Lemma 60.3.2: the explicit bilinear triple extension carries divided powers, and the
first-coordinate inclusion is a divided-power morphism. -/
@[stacks 07HI] #check
  (DividedPowers.BilinearExtension.inclusion_isDPMorphism :
    ∀ {A : Type u} {M : Type v} {N : Type w} [CommRing A] [AddCommGroup M] [Module A M]
      [AddCommGroup N] [Module A N] {I : Ideal A} (gamma : DividedPowers I)
      (q : M →ₗ[A] M →ₗ[A] N),
      DividedPowers.IsDPMorphism gamma
        (DividedPowers.BilinearExtension.dividedPowers q gamma)
        (DividedPowers.BilinearExtension.inclusion q))
