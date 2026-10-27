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
      (∀ f ∈ E', f ∉ x.asIdeal) ∧ (∀ f ∈ E'', f ∈ x.asIdeal) := by
  simp [vanishingStratum, mem_zeroLocus, Set.subset_def]

/-- Membership in a vanishing-pattern stratum is equivalent to the corresponding residue-field
elements being nonzero and zero, respectively. -/
theorem mem_vanishingStratum_iff {E' E'' : Set A} {x : PrimeSpectrum A} :
    x ∈ vanishingStratum E' E'' ↔
      (∀ f ∈ E', algebraMap A x.asIdeal.ResidueField f ≠ 0) ∧
        (∀ f ∈ E'', algebraMap A x.asIdeal.ResidueField f = 0) := by
  simp only [mem_vanishingStratum, ne_eq, Ideal.algebraMap_residueField_eq_zero]

/-- For finite subsets, a vanishing-pattern stratum is the intersection of a basic open defined by
the product of the first subset and the zero locus of the ideal spanned by the second subset. -/
theorem vanishingStratum_eq_basicOpen_inf_zeroLocus (E' E'' : Finset A) :
    vanishingStratum E' E'' =
      (basicOpen (∏ f ∈ E', f) : Set (PrimeSpectrum A)) ∩
        zeroLocus (Ideal.span (E'' : Set A) : Set A) := by
  ext x
  simp [mem_vanishingStratum, zeroLocus_span, mem_zeroLocus,
    Ideal.IsPrime.prod_mem_iff, Set.subset_def]

/-- The vanishing-pattern stratum is the intersection of the basic opens indexed by the first
subset and the principal zero loci indexed by the second subset. -/
theorem vanishingStratum_eq_iInter (E' E'' : Set A) :
    vanishingStratum E' E'' =
      (⋂ f ∈ E', (basicOpen f : Set (PrimeSpectrum A))) ∩
        (⋂ f ∈ E'', zeroLocus ({f} : Set A)) := by
  ext x
  simp [mem_vanishingStratum, mem_zeroLocus, Set.subset_def]

/-- The intersection presentation of a finite vanishing-pattern stratum equals its product and
ideal-span presentation. -/
theorem stratum_eq (E' E'' : Finset A) :
    (⋂ f ∈ E', (basicOpen f : Set (PrimeSpectrum A))) ∩
        (⋂ f ∈ E'', zeroLocus ({f} : Set A)) =
      (basicOpen (∏ f ∈ E', f) : Set (PrimeSpectrum A)) ∩
        zeroLocus ((Ideal.span (E'' : Set A) : Set A)) := by
  exact (vanishingStratum_eq_iInter (E' : Set A) (E'' : Set A)).symm.trans
    (vanishingStratum_eq_basicOpen_inf_zeroLocus E' E'')

/-- A vanishing-pattern stratum is locally closed when its nonvanishing indexing subset is finite.
-/ 
theorem isLocallyClosed_vanishingStratum {E' : Set A} (hE' : E'.Finite) (E'' : Set A) :
    IsLocallyClosed (vanishingStratum E' E'') := by
  exact ⟨_, _, hE'.isOpen_biInter (fun _ _ ↦ isOpen_basicOpen),
    isClosed_zeroLocus E'', rfl⟩

/-- A vanishing-pattern stratum is constructible when both indexing subsets are finite. -/
theorem isConstructible_vanishingStratum {E' E'' : Set A}
    (hE' : E'.Finite) (hE'' : E''.Finite) :
    IsConstructible (vanishingStratum E' E'') := by
  rw [vanishingStratum_eq_iInter]
  refine (IsConstructible.biInter hE' (fun _ _ ↦ isConstructible_basicOpen)).inter ?_
  refine IsConstructible.biInter hE'' (fun f _ ↦ ?_)
  simpa only [basicOpen_eq_zeroLocus_compl, compl_compl] using
    (isConstructible_basicOpen (f := f)).compl

/-- Every point of a prime spectrum belongs to a unique vanishing-pattern stratum indexed by a
subset of a given finite subset of the ring. -/
theorem existsUnique_mem_vanishingStratum {A : Type u} [CommRing A]
    (E : Set A) (hE : E.Finite) (x : PrimeSpectrum A) :
    ∃! E' : Set A, E' ⊆ E ∧ x ∈ vanishingStratum E' (E \ E') := by
  classical
  refine ⟨E \ (x.asIdeal : Set A), ⟨sdiff_subset, ?_⟩, ?_⟩
  · show x ∈ vanishingStratum (E \ (x.asIdeal : Set A)) (E \ (E \ (x.asIdeal : Set A)))
    rw [mem_vanishingStratum]
    refine ⟨fun _ hf ↦ hf.2, fun f hf ↦ ?_⟩
    by_contra hfp
    exact hf.2 ⟨hf.1, hfp⟩
  · change ∀ F, F ⊆ E ∧ x ∈ vanishingStratum F (E \ F) → F = E \ (x.asIdeal : Set A)
    rintro F ⟨hFE, hxF⟩
    obtain ⟨hnonzero, hzero⟩ := mem_vanishingStratum.mp hxF
    apply Set.Subset.antisymm
    · show F ⊆ E \ (x.asIdeal : Set A)
      exact fun f hf ↦ ⟨hFE hf, hnonzero f hf⟩
    · show E \ (x.asIdeal : Set A) ⊆ F
      rintro f ⟨hfE, hfp⟩
      by_contra hfF
      exact hfp (hzero f ⟨hfE, hfF⟩)

/-- For a finite subset of a commutative ring, the vanishing-pattern strata cover its prime
spectrum when indexed by all of its subsets. -/
theorem iUnion_vanishingStratum_eq_univ {A : Type u} [CommRing A] (E : Set A) (hE : E.Finite) :
    ⋃ (E' : Set A) (_ : E' ⊆ E), vanishingStratum E' (E \ E') =
      (univ : Set (PrimeSpectrum A)) := by
  refine Set.eq_univ_of_forall (fun x ↦ ?_)
  obtain ⟨E', ⟨hE', hx⟩, _⟩ := existsUnique_mem_vanishingStratum E hE x
  exact mem_iUnion.mpr ⟨E', mem_iUnion.mpr ⟨hE', hx⟩⟩

/-- For a finite subset of a commutative ring, the vanishing-pattern strata indexed by its
subsets are pairwise disjoint. -/
theorem pairwiseDisjoint_vanishingStratum {A : Type u} [CommRing A] (E : Set A) (hE : E.Finite) :
    {E' : Set A | E' ⊆ E}.PairwiseDisjoint
      (fun E' ↦ vanishingStratum E' (E \ E')) := by
  rw [Set.pairwiseDisjoint_iff]
  rintro E₁ hE₁ E₂ hE₂ ⟨x, hx₁, hx₂⟩
  obtain ⟨F, _, hUnique⟩ := existsUnique_mem_vanishingStratum E hE x
  exact (hUnique E₁ ⟨hE₁, hx₁⟩).trans (hUnique E₂ ⟨hE₂, hx₂⟩).symm

end PrimeSpectrum
