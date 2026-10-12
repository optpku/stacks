/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.Ideal.GoingUp

@[expose] public section

universe u v

/- Exercise 111.58.3: if `A` is local with maximal ideal `m` and `A → B` is a finite injective
ring map, then some prime ideal `q` of `B` satisfies `q.comap f = IsLocalRing.maximalIdeal A`. -/
@[stacks 0D5I]
#check (RingHom.exists_comap_eq_maximalIdeal_of_finite :
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsLocalRing A]
    {f : A →+* B}, f.Finite → Function.Injective f →
      ∃ q : Ideal B, q.IsPrime ∧ q.comap f = IsLocalRing.maximalIdeal A)
