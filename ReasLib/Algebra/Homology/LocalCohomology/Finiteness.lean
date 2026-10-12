/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.RingTheory.Ideal.Quotient.Prime

universe u

@[expose] public section

namespace localCohomology

/-- For a finite module `M` over a Noetherian ring `A`, degree-one local cohomology
supported on `V(I)` is finite if and only if, for each associated prime `p` of
`M` outside `V(I)` and each prime `q` containing both `p` and `I`, the
maximal-ideal completion of the localization of `A ⧸ p` at the prime induced by
`q` has no associated prime whose quotient has Krull dimension one. -/
theorem finite_one_iff_completionAssociatedPrimes
    {A M : Type u} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) :
    Module.Finite A ((localCohomology I 1).obj (ModuleCat.of A M)) ↔
      ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M →
        p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
          ∀ (q : PrimeSpectrum A) (h_pq : p.asIdeal ≤ q.asIdeal)
            (h_Iq : I ≤ q.asIdeal),
            let qbar := PrimeSpectrum.quotientOfLE p.asIdeal q h_pq
            let B := Localization.AtPrime qbar.asIdeal
            let Bhat := AdicCompletion (IsLocalRing.maximalIdeal B) B
            ∀ r ∈ associatedPrimes Bhat Bhat,
              ringKrullDim (Bhat ⧸ r) ≠ 1 := sorry

end localCohomology
