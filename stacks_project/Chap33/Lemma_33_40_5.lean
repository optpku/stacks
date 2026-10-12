/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Normalization.OneDimensional.Branches

@[expose] public section

universe u

/- Lemma 33.40.5 (1): the normalization delta invariant of a strictly henselian
reduced Nagata local ring of dimension one is at least its number of geometric
branches minus one. -/
@[stacks 0C42] #check
  (Normalization.OneDimensional.StrictHenselian.deltaInvariant_ge_minimalPrimes_sub_one :
    ∀ {A : Type u} [CommRing A] [StrictHenselianLocalRing A] [NagataRing A] [IsReduced A],
      ringKrullDim A = 1 →
        Normalization.deltaInvariant A ≥ (minimalPrimes A).encard - 1)

/- Lemma 33.40.5 (2): equality implies that the ring is a wedge of a nonempty
finite family of strictly henselian discrete valuation rings. -/
@[stacks 0C42] #check
  (Normalization.OneDimensional.StrictHenselian.exists_wedgeOf_dvrFamily_of_deltaInvariant_eq :
    ∀ {A : Type u} [CommRing A] [StrictHenselianLocalRing A] [NagataRing A] [IsReduced A],
      ringKrullDim A = 1 →
        Normalization.deltaInvariant A = (minimalPrimes A).encard - 1 →
          ∃ (m : ℕ) (As : LocalRing.Wedge.StrictHenselianDvrFamily m), As.IsWedgeOf A)
