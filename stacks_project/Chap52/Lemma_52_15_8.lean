/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.NeighborhoodCompletion
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry
open localCohomology

/- Lemma 52.15.8

Let `A` be a Noetherian ring, let `f ∈ 𝔞 ⊆ A`, and let `U = Spec(A) ∖ V(𝔞)`.
If `A` is `(f)`-adically complete, `f` is regular, and `H¹_𝔞(A / fA)` is finite
over `A`, then neighborhood completion along `f𝒪_U` is fully faithful on finite
locally free coherent modules. -/
@[stacks 0EKV] #check
  (AlgebraicGeometry.AffineAlgebraizationSetup.neighborhoodCompletionFullyFaithful_of_principal_finiteLocalCohomology :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (𝔞 : Ideal A) (f : A) (hf : f ∈ 𝔞)
      [IsAdicComplete (Ideal.span {f}) A]
      (h_regular : IsRegular f)
      [Module.Finite A
        ((localCohomology 𝔞 1).obj
          (ModuleCat.of A
            (A ⧸ (Ideal.span {f} • (⊤ : Submodule A A)))))] ,
      let S := AffineAlgebraizationSetup.ofPrincipal 𝔞 f hf
      AlgebraicGeometry.Scheme.CoherentCompletion.NeighborhoodCompletionFullyFaithful
        (AffineAlgebraizationSetup.idealOnOpen S))
