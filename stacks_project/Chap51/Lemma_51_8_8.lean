/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.LocalCohomology.Finiteness
import StacksCheckRecall

universe u

@[expose] public section

/- Lemma 51.8.8: degree-one local cohomology is finite exactly when, for every
 associated prime outside `V(I)`, every prime containing it and `I` gives a
 completed quotient localization with no associated-prime quotient of Krull
 dimension one. -/
@[stacks 0BL9] #check (localCohomology.finite_one_iff_completionAssociatedPrimes :
  ∀ {A M : Type u} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A),
    Module.Finite A ((localCohomology I 1).obj (ModuleCat.of A M)) ↔
      ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M →
        p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
          ∀ (q : PrimeSpectrum A) (h_pq : p.asIdeal ≤ q.asIdeal)
            (h_Iq : I ≤ q.asIdeal),
            let qbar := PrimeSpectrum.quotientOfLE p.asIdeal q h_pq
            let B := Localization.AtPrime qbar.asIdeal
            let Bhat := AdicCompletion (IsLocalRing.maximalIdeal B) B
            ∀ r ∈ associatedPrimes Bhat Bhat,
              ringKrullDim (Bhat ⧸ r) ≠ 1)
