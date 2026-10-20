module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.NeighborhoodCompletion
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

/- Lemma 52.24.1: completion is an equivalence on finite locally free coherent
objects over neighborhoods of the closed fiber under either the Serre/minimal-prime
or primewise depth-dimension hypotheses. -/
@[stacks 0EKY] #check
  (AlgebraicGeometry.AffineAlgebraizationSetup.completionEquivalenceOnFiniteLocallyFree_of_serreOrDepth :
    ∀
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (S : AffineAlgebraizationSetup A)
    (h_dualizing : DerivedCategory.HasCanonicalDualizingComplex A)
    [IsAdicComplete S.I A]
    (f : A)
    (h_I : S.I = Ideal.span ({f} : Set A))
    (h_a : S.a = IsLocalRing.maximalIdeal A)
    (h_alternative :
      (SerreConditionS (Localization.Away f) 2 ∧
        ∀ p : PrimeSpectrum A,
          p.asIdeal ∈ minimalPrimes A →
            f ∉ p.asIdeal →
              (4 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) ∨
      (∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus ({f} : Set A) →
          PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus ({f} : Set A) ≠
            {IsLocalRing.closedPoint A} →
            (3 : EInt) <
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal A)) : WithTop ℤ) : EInt) +
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (A ⧸ p.asIdeal)))),
    let IU := idealOnOpen S
    CoherentCompletion.NeighborhoodCompletionFullyFaithful IU ∧
      ∀ F : CoherentFormalModules S.U.toScheme IU,
        (∀ n : ℕ, CoherentFormalModules.IsFiniteLocallyFreeStage F n) →
          ∃ V : (CoherentCompletion.compactSupport IU).openNhds,
            (CoherentCompletion.onFiniteLocallyFree
              (IU.comap (Scheme.Opens.ι V.val))).essImage
                ((coherentFormalModulesRestrictionFunctor IU V.val).obj F))

end AlgebraicGeometry.AffineAlgebraizationSetup
