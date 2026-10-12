/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.PrimeAvoidance.Transcendence
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 37.31.1: for a finite pairwise-incomparable family of prime ideals,
an ideal avoiding each prime contains an element whose image in every residue
field is transcendental over the chosen subfield. -/
@[stacks 0GTE] #check
  (Ideal.exists_mem_transcendental_residueFields :
    {R : Type u} → [CommRing R] → {ι : Type v} → [Finite ι] →
      (p : ι → PrimeSpectrum R) →
      (∀ ⦃i j⦄, i ≠ j → ¬ (p i).asIdeal ≤ (p j).asIdeal) →
      (k : ∀ i, Subfield (p i).asIdeal.ResidueField) →
      (∀ i, ¬ Algebra.IsAlgebraic (k i) (p i).asIdeal.ResidueField) →
      (J : Ideal R) →
      (∀ i, ¬ J ≤ (p i).asIdeal) →
      ∃ x ∈ J, ∀ i, Transcendental (k i)
        (algebraMap R (p i).asIdeal.ResidueField x))
