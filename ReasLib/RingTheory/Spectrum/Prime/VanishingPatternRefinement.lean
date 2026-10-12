/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.VanishingStratum

/-!
# Refinements by vanishing-pattern strata

The vanishing-pattern cells associated to a finite subset of a commutative
ring refine finite constructible partitions of its prime spectrum.
-/

@[expose] public section

open Set Topology

universe u v

namespace PrimeSpectrum

/-- The vanishing-pattern stratification of a subset `E ⊆ A` refines an indexed
family `T` if every nonempty cell `vanishingStratum E' (E \ E')` is contained
in some `T i`. Empty cells are not required to pick an index. -/
def vanishingPatternRefines {A : Type u} [CommRing A] (E : Set A)
    {ι : Type v} (T : ι → Set (PrimeSpectrum A)) : Prop :=
  ∀ ⦃E' : Set A⦄, E' ⊆ E → (vanishingStratum E' (E \ E')).Nonempty →
    ∃ i, vanishingStratum E' (E \ E') ⊆ T i

/-- For a partition of the prime spectrum, refinement by vanishing-pattern
strata is equivalent to constancy of each part on points with equal patterns.
-/
theorem vanishingPatternRefines_iff {A : Type u} [CommRing A] (E : Set A)
    {ι : Type v} (T : ι → Set (PrimeSpectrum A))
    (h_disjoint : Pairwise fun i j ↦ Disjoint (T i) (T j))
    (h_cover : (⋃ i, T i) = univ) :
    vanishingPatternRefines E T ↔
      ∀ x y : PrimeSpectrum A,
        (∀ f ∈ E, f ∈ x.asIdeal ↔ f ∈ y.asIdeal) →
          ∀ i, x ∈ T i ↔ y ∈ T i := sorry

/-- Enlarging the indexing set preserves refinement by vanishing-pattern
strata. -/
theorem vanishingPatternRefines_mono {A : Type u} [CommRing A]
    {E F : Set A} {ι : Type v} (T : ι → Set (PrimeSpectrum A))
    (hEF : E ⊆ F) (hE : vanishingPatternRefines E T) :
    vanishingPatternRefines F T := sorry

/-- Every finite partition of `PrimeSpectrum A` by constructible subsets is
refined by the vanishing-pattern stratification of some finite subset of `A`.
-/
theorem exists_finite_vanishingPatternRefines {A : Type u} [CommRing A]
    {ι : Type v} [Finite ι] (T : ι → Set (PrimeSpectrum A))
    (h_disjoint : Pairwise fun i j ↦ Disjoint (T i) (T j))
    (h_cover : (⋃ i, T i) = univ) (h_cons : ∀ i, IsConstructible (T i)) :
    ∃ E : Finset A, vanishingPatternRefines (E : Set A) T := sorry

end PrimeSpectrum
