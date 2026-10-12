/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.LocalCohomology.Cutoff

universe u v

/- 51.11.1.1: For a finite module `M` over a Noetherian ring `A`, the invariant
`s_{A,I}(M)` is the minimum of the localized depth plus quotient-local dimension
over chains of primes from outside `V(I)` to inside `V(I)`. -/
@[stacks 0BJR] #check (Module.LocalCohomology.cutoff :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A],
    (I : Ideal A) → (M : Type v) → [AddCommGroup M] → [Module A M] →
      [Module.Finite A M] → WithBot ℕ∞)
