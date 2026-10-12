/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.NeighborhoodComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open localCohomology

universe u

/- Lemma 52.12.5: let `U = Spec A ∖ V(𝔞)`. If `f ∈ 𝔞`, `M` is finite,
`A` is `(f)`-adically complete, multiplication by `f` on `M` is injective, and
`H¹_𝔞(M / fM)` is finite, then the canonical map from the colimit of sections
over neighborhoods of `U ∩ V(f)` to the positive quotient-section inverse limit
is bijective. -/
@[stacks 0EIH]
#check (AlgebraicGeometry.AffineAlgebraizationSetup.neighborhoodComparison_bijective_of_principal :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (𝔞 : Ideal A) (f : A) (hf : f ∈ 𝔞) (M : ModuleCat A)
    [Module.Finite A M] [IsAdicComplete (Ideal.span {f}) A]
    (h_regular : IsSMulRegular M f)
    [Module.Finite A
      ((localCohomology 𝔞 1).obj
        (ModuleCat.of A
          (M ⧸ (Ideal.span {f} • (⊤ : Submodule A M)))))] ,
    Function.Bijective
      (AlgebraicGeometry.AffineAlgebraizationSetup.neighborhoodComparison
        (AlgebraicGeometry.AffineAlgebraizationSetup.ofPrincipal 𝔞 f hf)
        ((AlgebraicGeometry.tilde M).restrict
          (AlgebraicGeometry.AffineAlgebraizationSetup.ofPrincipal 𝔞 f hf).U.ι)))
