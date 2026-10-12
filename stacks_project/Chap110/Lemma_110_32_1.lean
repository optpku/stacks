/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Ideal.LocallyPrincipal

@[expose] public section

universe u

/- Lemma 110.32.1: there exists a domain `A` and a nonzero ideal `I ⊆ A` such that
`I.localizationAtPrime q` is a principal ideal for every prime `q` of `A`, but `I` is
not invertible as an `A`-module. -/
@[stacks 0CC0]
#check (Module.Invertible.exists_ideal_locallyPrincipal_not_invertible :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (I : Ideal A),
      I ≠ ⊥ ∧ (∀ q : PrimeSpectrum A, (I.localizationAtPrime q).IsPrincipal) ∧
        ¬ Module.Invertible A I)
