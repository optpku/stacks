/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.NeighborhoodComparison
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.PrincipalFiniteLocalCohomology
public import Mathlib.Algebra.Regular.Defs

@[expose] public section

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

end AlgebraicGeometry.AffineAlgebraizationSetup
