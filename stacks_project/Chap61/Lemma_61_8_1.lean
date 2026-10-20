module

public import ReasLib.Algebra.IndEtaleEnvelope.Iteration
import StacksCheckRecall

@[expose] public section

universe u

open Algebra

/- Lemma 61.8.1: Given a ring A there exists a faithfully flat ind-étale
A-algebra C such that every faithfully flat étale ring map C → B has a retraction. -/
@[stacks 097R] #check
  (Algebra.IndEtaleEnvelope.exists_faithfullyFlat_indEtale_retraction :
    ∀ (A : Type u) [CommRing A],
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
        Module.FaithfullyFlat A C ∧ (algebraMap A C).IndEtale ∧
        HasFaithfullyFlatEtaleRetraction C)
