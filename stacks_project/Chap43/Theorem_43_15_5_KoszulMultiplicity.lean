/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.KoszulMultiplicity

open scoped BigOperators

universe u

#check (Ideal.HilbertSamuel.koszulHomology_isFiniteLength :
  {R : Type u} → [CommRing R] → [IsLocalRing R] → [IsNoetherianRing R] →
    {M : Type u} → [AddCommGroup M] → [Module R M] → [Module.Finite R M] →
      (r : ℕ) → (I : Ideal R) → (f : Fin r → R) →
        Ideal.span (Set.range f) = I → I.IsIdealOfDefinition → (i : ℕ) →
          IsFiniteLength R
            ((RingTheory.Sequence.koszulComplexOnTensorLeft R M f).homology i))

#check (Ideal.HilbertSamuel.multiplicityInDegree_eq_koszulHomologyLengthSum :
  {R : Type u} → [CommRing R] → [IsLocalRing R] → [IsNoetherianRing R] →
    {M : Type u} → [AddCommGroup M] → [Module R M] → [Module.Finite R M] →
      (r : ℕ) → (I : Ideal R) → (f : Fin r → R) →
        Ideal.span (Set.range f) = I → I.IsIdealOfDefinition →
          Ideal.HilbertSamuel.multiplicityInDegree I M r =
            ((∑ i ∈ Finset.range (r + 1), (Int.negOnePow i : ℤ) *
              ((Module.length R
                ((RingTheory.Sequence.koszulComplexOnTensorLeft R M f).homology i)).toNat : ℤ) : ℤ) : ℚ))
