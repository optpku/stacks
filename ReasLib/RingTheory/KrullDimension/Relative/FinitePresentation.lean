/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.KrullDimension.Relative.FiniteType

@[expose] public section

/-!
# Finite-presentation relative-dimension loci

This leaf owns the global topological finiteness properties of a bounded
relative-dimension locus for a finitely presented algebra.
-/

noncomputable section

universe u v

namespace RelativeDimensionAtLELocus

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- For a finitely presented algebra, the locus where relative dimension is at most `n` is open. -/
@[stacks 00QJ "openness of the bounded relative-dimension locus"]
theorem isOpen_of_finitePresentation [Algebra.FinitePresentation R S] (n : ℕ) :
    IsOpen (relativeDimensionAtLELocus R S n) := sorry

/-- For a finitely presented algebra, the locus where relative dimension is at most `n` is
quasi-compact. -/
@[stacks 00QJ "quasi-compactness of the bounded relative-dimension locus"]
theorem isCompact_of_finitePresentation [Algebra.FinitePresentation R S] (n : ℕ) :
    IsCompact (relativeDimensionAtLELocus R S n) := sorry

/-- Lemma 10.125.8, tag 00QJ: for a finitely presented algebra, the bounded
relative-dimension locus is open and quasi-compact. -/
@[stacks 00QJ "finite-presentation relative-dimension locus"]
theorem isOpen_isCompact_of_finitePresentation [Algebra.FinitePresentation R S] (n : ℕ) :
    IsOpen (relativeDimensionAtLELocus R S n) ∧
      IsCompact (relativeDimensionAtLELocus R S n) := sorry

end RelativeDimensionAtLELocus
