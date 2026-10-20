/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.VanishingStratum
import StacksCheckRecall

@[expose] public section

open Set

universe u

/- 61.5.1.2 (1): for a ring `A` and a finite subset `E ⊆ A`, the affine space
`X = Spec(A)` is covered by the vanishing-pattern strata `vanishingStratum E' (E \ E')`
as `E'` runs over subsets of `E`. -/
@[stacks 096X] #check (PrimeSpectrum.iUnion_vanishingStratum_eq_univ :
  ∀ {A : Type u} [CommRing A] (E : Set A), E.Finite →
    ⋃ (E' : Set A) (_ : E' ⊆ E), PrimeSpectrum.vanishingStratum E' (E \ E') =
      (univ : Set (PrimeSpectrum A)))

/- 61.5.1.2 (2): the vanishing-pattern strata `vanishingStratum E' (E \ E')` attached to
complementary decompositions of a finite subset `E ⊆ A` are pairwise disjoint. -/
@[stacks 096X] #check (PrimeSpectrum.pairwiseDisjoint_vanishingStratum :
  ∀ {A : Type u} [CommRing A] (E : Set A), E.Finite →
    {E' : Set A | E' ⊆ E}.PairwiseDisjoint
      (fun E' ↦ PrimeSpectrum.vanishingStratum E' (E \ E')))

/- Every point of `PrimeSpectrum A` lies in a unique vanishing-pattern stratum for a finite
subset `E ⊆ A`. -/
#check (PrimeSpectrum.existsUnique_mem_vanishingStratum :
  ∀ {A : Type u} [CommRing A] (E : Set A), E.Finite → (x : PrimeSpectrum A) →
    ∃! E' : Set A, E' ⊆ E ∧ x ∈ PrimeSpectrum.vanishingStratum E' (E \ E'))
