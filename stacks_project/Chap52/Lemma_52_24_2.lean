/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.NeighborhoodCompletion
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

/- Lemma 52.24.2: the two clauses present full faithfulness and essential
surjectivity after shrinking to an open neighborhood of the restricted closed
fiber, with the algebraization remaining finite locally free. -/
@[stacks 0EKZ] #check
  (AlgebraicGeometry.AffineAlgebraizationSetup.completionEquivalenceOnFiniteLocallyFree :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
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
          (A ⧸ (Ideal.span {f} • (⊤ : Submodule A A)))))] ,
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
                  (coherentFormalModulesRestrictionFunctor IU V.val).obj F))

end AlgebraicGeometry.AffineAlgebraizationSetup
