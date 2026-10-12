/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Lemma_52_15_7
public import stacks_project.Chap52.Lemma_52_16_11
public import stacks_project.Chap52.Lemma_52_20_6
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

/-- Lemma 52.24.1: for a complete Noetherian local ring with a dualizing complex
and principal ideal `S.I = (f)`, either of the stated Serre/minimal-prime or
primewise depth-dimension conditions makes completion an equivalence on finite
locally free coherent objects over neighborhoods of the closed fiber. -/
@[stacks 0EKY]
theorem completionEquivalenceOnFiniteLocallyFree_of_serreOrDepth
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (S : AffineAlgebraizationSetup A)
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
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
                  (ringKrullDim (A ⧸ p.asIdeal)))) :
    let IU := idealOnOpen S
    CoherentCompletion.NeighborhoodCompletionFullyFaithful IU ∧
      ∀ F : CoherentFormalModules S.U.toScheme IU,
        (∀ n : ℕ, CoherentFormalModules.IsFiniteLocallyFreeStage F n) →
          ∃ V : (CoherentCompletion.compactSupport IU).openNhds,
            (CoherentCompletion.onFiniteLocallyFree
              (IU.comap (Scheme.Opens.ι V.val))).essImage
                ((coherentFormalModulesRestrictionFunctor IU V.val).obj F) := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
