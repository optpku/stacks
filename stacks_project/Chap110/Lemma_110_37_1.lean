/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.FiniteType.Counterexample
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 110.37.1: there exists a local ring `A`, a finite type `A`-algebra `B`, and a prime
`q` of `B` lying over the maximal ideal of `A` such that `Localization.AtPrime q` is flat over
`A`, while for every `g ∉ q` the principal localization `Localization.Away g` is neither of
finite presentation nor flat over `A`. -/
@[stacks 05G2] #check
  (Algebra.FiniteType.exists_flat_atPrime_not_flat_away :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B)
      (_ : IsLocalRing A) (q : Ideal B) (_ : q.IsPrime),
      Algebra.FiniteType A B ∧
        Ideal.comap (algebraMap A B) q = IsLocalRing.maximalIdeal A ∧
        Module.Flat A (Localization.AtPrime q) ∧
        ∀ g : B, g ∉ q →
          ¬ Algebra.FinitePresentation A (Localization.Away g) ∧
            ¬ Module.Flat A (Localization.Away g))
