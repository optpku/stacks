/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.Counterexample
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 110.12.7: there exists a commutative ring `A` that is `I`-adically
complete for a principal ideal `I`, together with an element `f : A`, such that
the `I`-adic completion of `Localization.Away f` is not flat over `A`. -/
@[stacks 0ALE] #check
  (AdicCompletion.exists_principal_away_notFlat :
    ∃ (A : Type u) (_ : CommRing A) (I : Ideal A) (f : A),
      I.IsPrincipal ∧ IsAdicComplete I A ∧
        ¬ Module.Flat A (AdicCompletion I (Localization.Away f)))
