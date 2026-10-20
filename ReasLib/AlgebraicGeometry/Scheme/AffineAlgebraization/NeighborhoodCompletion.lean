/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.NeighborhoodComparison
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.PrincipalFiniteLocalCohomology
public import Mathlib.Algebra.Regular.Defs
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.CanonicalExistence
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.Order.WithBotTop

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open localCohomology

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

/-- Under principal completeness, regularity, and finite local cohomology, neighborhood
completion is fully faithful on finite locally free objects. -/
theorem neighborhoodCompletionFullyFaithful_of_principal_finiteLocalCohomology
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (𝔞 : Ideal A) (f : A) (hf : f ∈ 𝔞)
    [IsAdicComplete (Ideal.span {f}) A]
    (h_regular : IsRegular f)
    [Module.Finite A
      ((localCohomology 𝔞 1).obj
        (ModuleCat.of A
          (A ⧸ (Ideal.span {f} • (⊤ : Submodule A A)))))] :
    let S := ofPrincipal 𝔞 f hf
    CoherentCompletion.NeighborhoodCompletionFullyFaithful (idealOnOpen S) := sorry

/-- Under the principal regular and complete setup, finite local cohomology in
degrees one and two gives neighborhood completion equivalence on finite locally
free objects. -/
theorem completionEquivalenceOnFiniteLocallyFree
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (𝔞 : Ideal A) (f : A) (hf : f ∈ 𝔞)
    [IsAdicComplete (Ideal.span {f}) A]
    (h_regular : IsRegular f)
    [Module.Finite A
      ((localCohomology 𝔞 1).obj
        (ModuleCat.of A
          (A ⧸ (Ideal.span {f} • (⊤ : Submodule A A)))))]
    [Module.Finite A
      ((localCohomology 𝔞 2).obj
        (ModuleCat.of A
          (A ⧸ (Ideal.span {f} • (⊤ : Submodule A A)))))] :
    let S := ofPrincipal 𝔞 f hf
    let X := S.U.toScheme
    let IU := idealOnOpen S
    CoherentCompletion.NeighborhoodCompletionFullyFaithful IU ∧
      ∀ (F : CoherentFormalModules X IU),
        (∀ n : ℕ, CoherentFormalModules.IsFiniteLocallyFreeStage F n) →
          ∃ V : (CoherentCompletion.compactSupport IU).openNhds,
            ∃ E :
                (CoherentCompletion.finiteLocallyFree
                    (Opens.toScheme (V.val : X.Opens))).FullSubcategory,
              Nonempty
                ((CoherentCompletion.functor
                    (IU.comap (Opens.ι V.val))).obj E.obj ≅
                  (coherentFormalModulesRestrictionFunctor IU V.val).obj F) := sorry

/-- For a Noetherian local ring admitting a canonical dualizing complex and complete
along a principal ideal, either the Serre condition `(S₂)` away from the generator
with minimal-prime quotient dimension at least four, or the primewise strict
depth-plus-dimension bound, makes neighborhood completion fully faithful and
essentially surjective on finite locally free coherent objects after shrinking
around the closed fiber. -/
theorem completionEquivalenceOnFiniteLocallyFree_of_serreOrDepth
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
