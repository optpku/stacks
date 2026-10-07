module

import StacksCheckRecall
public import ReasLib.RingTheory.Normalization.OneDimensional.Branches

@[expose] public section

universe u v

/- Lemma 33.40.6: the normalization delta invariant of a one-dimensional
reduced Nagata local ring is at least its number of geometric branches minus
one. -/
@[stacks 0C43] #check
  (Normalization.OneDimensional.StrictHenselization.deltaInvariant_ge_minimalPrimes_sub_one :
    ∀ {A : Type u} {Ash : Type v} [CommRing A] [IsLocalRing A] [NagataRing A]
      [IsReduced A] [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash],
      ringKrullDim A = 1 →
        Normalization.deltaInvariant A ≥ geometricBranchNumber A Ash - 1)
