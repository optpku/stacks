module

public import ReasLib.RingTheory.Spectrum.Prime.VanishingPatternRefinement
import StacksCheckRecall

@[expose] public section

universe u v

open Set Topology

/- Lemma 61.5.2: let `X = Spec(A)`. Given any finite stratification
`X = ⨿ T i` by constructible subsets, there exists a finite subset `E ⊆ A`
such that the vanishing-pattern stratification (61.5.1.2)
`X = ⨿ vanishingStratum E' (E \ E')` as `E' ⊆ E` refines `X = ⨿ T i`. -/
@[stacks 096Y] #check
  (PrimeSpectrum.exists_finite_vanishingPatternRefines :
    {A : Type u} → [CommRing A] → {ι : Type v} → [Finite ι] →
      (T : ι → Set (PrimeSpectrum A)) →
        Pairwise (fun i j ↦ Disjoint (T i) (T j)) →
          ((⋃ i, T i) = univ) → (∀ i, IsConstructible (T i)) →
            ∃ E : Finset A, PrimeSpectrum.vanishingPatternRefines (E : Set A) T)
