/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.NeighborhoodComparison
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Neighborhood
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.CanonicalExistence
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
public import ReasLib.RingTheory.Spectrum.Prime.AssociatedSubset
public import ReasLib.RingTheory.Ideal.Localization
public import ReasLib.RingTheory.Depth
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.Order.WithBotTop

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- For nested ideals `I ≤ 𝔞` in a Noetherian ring that is `I`-adically complete and
admits a canonical dualizing complex, the associated-prime local dimension bound
along `V(𝔞)` implies that neighborhood completion on `Spec(A) ∖ V(𝔞)` is fully
faithful on finite locally free coherent modules. -/
theorem neighborhoodCompletionFullyFaithful_of_associatedPrimeDimension
    (S : AffineAlgebraizationSetup A)
    (h_dualizing : DerivedCategory.HasCanonicalDualizingComplex A)
    [IsAdicComplete S.I A]
    (h_dimension : ∀ p q : PrimeSpectrum A,
      p.asIdeal ∈ associatedPrimes A A →
        ¬ S.I ≤ p.asIdeal →
          p ∉ PrimeSpectrum.associatedSubset S.I S.a →
            q ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (S.a : Set A) →
              ((Ideal.LocalCohomology.dimension S.I
                  S.I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (p.asIdeal.quotientAtPrime q))) :
    CoherentCompletion.NeighborhoodCompletionFullyFaithful
      (AffineAlgebraizationSetup.idealOnOpen S) := sorry

/-- For nested ideals `I ≤ 𝔞` in an `I`-adically complete Noetherian ring admitting
a canonical dualizing complex, the strict associated-prime dimension bound along
`V(𝔞)` and depth at least two at primes outside `V(I)` whose intersection with
`V(I)` lies in `V(𝔞)` imply that completion on `Spec(A) ∖ V(𝔞)` is fully faithful
on finite locally free coherent modules. -/
theorem completionFullyFaithful_of_associatedPrimeDimension
    (S : AffineAlgebraizationSetup A)
    (h_dualizing : DerivedCategory.HasCanonicalDualizingComplex A)
    [IsAdicComplete S.I A]
    (h_dimension : ∀ p q : PrimeSpectrum A,
      p.asIdeal ∈ associatedPrimes A A →
        ¬ S.I ≤ p.asIdeal →
          p ∉ PrimeSpectrum.associatedSubset S.I S.a →
            q ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (S.a : Set A) →
              ((Ideal.LocalCohomology.dimension S.I
                  S.I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (p.asIdeal.quotientAtPrime q)))
    (h_depth : ∀ p : PrimeSpectrum A,
      ¬ S.I ≤ p.asIdeal →
        p ∈ PrimeSpectrum.associatedSubset S.I S.a →
          (2 : ℕ∞) ≤ moduleDepth (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal A)) :
    Nonempty (Scheme.CoherentCompletion.onFiniteLocallyFree
      (idealOnOpen S)).FullyFaithful := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
