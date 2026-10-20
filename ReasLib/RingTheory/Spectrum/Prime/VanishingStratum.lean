/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
Vanishing-pattern strata of the prime spectrum are intersections of basic opens with zero loci.
-/

@[expose] public section

open Set Topology

universe u

namespace PrimeSpectrum

variable {A : Type u} [CommRing A]

/-- The vanishing-pattern stratum of two subsets of a commutative ring is the intersection of
the basic opens indexed by the first subset with the zero locus of the second subset. -/
def vanishingStratum (E' E'' : Set A) : Set (PrimeSpectrum A) :=
  (⋂ f ∈ E', (basicOpen f : Set (PrimeSpectrum A))) ∩ zeroLocus E''

/-- Membership in a vanishing-pattern stratum is equivalent to nonvanishing on the first subset
and membership in the prime ideal on the second subset. -/
theorem mem_vanishingStratum {E' E'' : Set A} {x : PrimeSpectrum A} :
    x ∈ vanishingStratum E' E'' ↔
      (∀ f ∈ E', f ∉ x.asIdeal) ∧ (∀ f ∈ E'', f ∈ x.asIdeal) := sorry

/-- Membership in a vanishing-pattern stratum is equivalent to the corresponding residue-field
elements being nonzero and zero, respectively. -/
theorem mem_vanishingStratum_iff {E' E'' : Set A} {x : PrimeSpectrum A} :
    x ∈ vanishingStratum E' E'' ↔
      (∀ f ∈ E', algebraMap A x.asIdeal.ResidueField f ≠ 0) ∧
        (∀ f ∈ E'', algebraMap A x.asIdeal.ResidueField f = 0) := sorry

/-- For finite subsets, a vanishing-pattern stratum is the intersection of a basic open defined by
the product of the first subset and the zero locus of the ideal spanned by the second subset. -/
theorem vanishingStratum_eq_basicOpen_inf_zeroLocus (E' E'' : Finset A) :
    vanishingStratum E' E'' =
      (basicOpen (∏ f ∈ E', f) : Set (PrimeSpectrum A)) ∩
        zeroLocus (Ideal.span (E'' : Set A) : Set A) := sorry

/-- The vanishing-pattern stratum is the intersection of the basic opens indexed by the first
subset and the principal zero loci indexed by the second subset. -/
theorem vanishingStratum_eq_iInter (E' E'' : Set A) :
    vanishingStratum E' E'' =
      (⋂ f ∈ E', (basicOpen f : Set (PrimeSpectrum A))) ∩
        (⋂ f ∈ E'', zeroLocus ({f} : Set A)) := sorry

/-- The intersection presentation of a finite vanishing-pattern stratum equals its product and
ideal-span presentation. -/
theorem stratum_eq (E' E'' : Finset A) :
    (⋂ f ∈ E', (basicOpen f : Set (PrimeSpectrum A))) ∩
        (⋂ f ∈ E'', zeroLocus ({f} : Set A)) =
      (basicOpen (∏ f ∈ E', f) : Set (PrimeSpectrum A)) ∩
        zeroLocus ((Ideal.span (E'' : Set A) : Set A)) := sorry

/-- A vanishing-pattern stratum is locally closed when its nonvanishing indexing subset is finite.
-/ 
theorem isLocallyClosed_vanishingStratum {E' : Set A} (hE' : E'.Finite) (E'' : Set A) :
    IsLocallyClosed (vanishingStratum E' E'') := sorry

/-- A vanishing-pattern stratum is constructible when both indexing subsets are finite. -/
theorem isConstructible_vanishingStratum {E' E'' : Set A}
    (hE' : E'.Finite) (hE'' : E''.Finite) :
    IsConstructible (vanishingStratum E' E'') := sorry

/-- Every point of a prime spectrum belongs to a unique vanishing-pattern stratum indexed by a
subset of a given finite subset of the ring. -/
theorem existsUnique_mem_vanishingStratum {A : Type u} [CommRing A]
    (E : Set A) (hE : E.Finite) (x : PrimeSpectrum A) :
    ∃! E' : Set A, E' ⊆ E ∧ x ∈ vanishingStratum E' (E \ E') := sorry

/-- For a finite subset of a commutative ring, the vanishing-pattern strata cover its prime
spectrum when indexed by all of its subsets. -/
theorem iUnion_vanishingStratum_eq_univ {A : Type u} [CommRing A] (E : Set A) (hE : E.Finite) :
    ⋃ (E' : Set A) (_ : E' ⊆ E), vanishingStratum E' (E \ E') =
      (univ : Set (PrimeSpectrum A)) := sorry

/-- For a finite subset of a commutative ring, the vanishing-pattern strata indexed by its
subsets are pairwise disjoint. -/
theorem pairwiseDisjoint_vanishingStratum {A : Type u} [CommRing A] (E : Set A) (hE : E.Finite) :
    {E' : Set A | E' ⊆ E}.PairwiseDisjoint
      (fun E' ↦ vanishingStratum E' (E \ E')) := sorry

end PrimeSpectrum
