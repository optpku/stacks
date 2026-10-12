/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.Retraction
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 61.8.4: if every faithfully flat étale ring map out of a ring `A` has a
retraction, then the same is true for every quotient ring `A ⧸ I`. -/
@[stacks 097U] #check (Algebra.HasFaithfullyFlatEtaleRetraction.quotient :
  ∀ {R : Type u} [CommRing R] [Algebra.HasFaithfullyFlatEtaleRetraction R]
    (I : Ideal R), Algebra.HasFaithfullyFlatEtaleRetraction (R ⧸ I))
