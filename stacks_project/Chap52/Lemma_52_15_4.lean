module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.AssociatedPrimeCompletion
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped ENat

noncomputable section

universe u

/- Lemma 52.15.4: for nested ideals `I ≤ 𝔞` in a Noetherian ring `A`, if `A` is
`I`-adically complete, has a dualizing complex, and satisfies the stated dimension
and depth bounds in the two associated-subset cases, completion on
`U = Spec(A) ∖ V(𝔞)` is fully faithful on finite locally free coherent modules. -/
@[stacks 0EKQ] #check
  (AlgebraicGeometry.AffineAlgebraizationSetup.completionFullyFaithful_of_associatedPrimeDimension :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
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
            (LocalizedModule.AtPrime p.asIdeal A)),
    Nonempty (Scheme.CoherentCompletion.onFiniteLocallyFree
      (AffineAlgebraizationSetup.idealOnOpen S)).FullyFaithful)
