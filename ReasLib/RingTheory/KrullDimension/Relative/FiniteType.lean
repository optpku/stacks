/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.KrullDimension.Relative.QuasiFinite

@[expose] public section

/-!
# Finite-type relative-dimension loci

For a finite-type algebra, this leaf provides the local neighborhood and basic-open
forms of upper semicontinuity for the relative-dimension locus.
-/

noncomputable section

open TopologicalSpace

universe u v

namespace RelativeDimensionAt

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.125.6, tag 00QH: if relative dimension at `q` is exactly `n`, then `q` has an open
neighborhood contained in the locus where relative dimension is at most `n`. -/
@[stacks 00QH "relative-dimension upper semicontinuity at a point"]
theorem exists_openNhdsOf_le_locus
    [Algebra.FiniteType R S] (n : ℕ) (q : PrimeSpectrum S)
    (hq : relativeDimensionAt R S q = (n : WithBot ℕ∞)) :
    ∃ U : OpenNhdsOf q, ∀ q' ∈ U, q' ∈ relativeDimensionAtLELocus R S n := sorry

/-- At a point where relative dimension is exactly `n`, a finite-type algebra has a principal
open neighborhood contained in the locus where relative dimension is at most `n`. -/
@[stacks 00QH "principal-open relative-dimension upper semicontinuity"]
theorem exists_basicOpen_subset_le_locus
    [Algebra.FiniteType R S] (n : ℕ) (q : PrimeSpectrum S)
    (hq : relativeDimensionAt R S q = (n : WithBot ℕ∞)) :
    ∃ g : S, g ∉ q.asIdeal ∧
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
        relativeDimensionAtLELocus R S n := sorry

end RelativeDimensionAt

namespace RelativeDimensionAtLELocus

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A point of a finite-type bounded relative-dimension locus has an open neighborhood contained
in the same locus. -/
@[stacks 00QH "bounded relative-dimension locus has local neighborhoods"]
theorem exists_openNhdsOf_mem
    [Algebra.FiniteType R S] (n : ℕ) (q : PrimeSpectrum S)
    (hq : q ∈ relativeDimensionAtLELocus R S n) :
    ∃ U : OpenNhdsOf q, ∀ q' ∈ U, q' ∈ relativeDimensionAtLELocus R S n := sorry

/-- A point of a finite-type bounded relative-dimension locus has a principal-open neighborhood
contained in the same locus. -/
@[stacks 00QH "principal-open refinement of a relative-dimension neighborhood"]
theorem exists_basicOpen_subset_of_mem
    [Algebra.FiniteType R S] (n : ℕ) (q : PrimeSpectrum S)
    (hq : q ∈ relativeDimensionAtLELocus R S n) :
    ∃ g : S, g ∉ q.asIdeal ∧
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
        relativeDimensionAtLELocus R S n := sorry

end RelativeDimensionAtLELocus
