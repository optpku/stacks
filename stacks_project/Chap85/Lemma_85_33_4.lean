module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_33_2_Hypercovering
public import stacks_project.Chap85.Lemma_85_33_4_Sections
public import stacks_project.Chap85.Lemma_85_33_4_Comparison

/-!
# Lemma 85.33.4

Let `S` be a scheme, `X` an algebraic space over `S`, and `U` a simplicial algebraic
space over `S`, with augmentation `a : U ⟶ X`. If `a` is an fppf hypercovering of `X`,
then for every `K` in `D⁺(X_étale)` the canonical comparison
`RΓ(X_étale, K) ⟶ RΓ(U_étale, a⁻¹ K)` is an isomorphism, where
`a : Sh(U_étale) ⟶ Sh(X_étale)` is the Section 85.32 spaces-étale augmentation.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Lemma 85.33.4: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `U`
be a simplicial algebraic space over `S`. Let `a : U ⟶ X` be an augmentation. If `a` is
an fppf hypercovering of `X`, then for `K` in `D⁺(X_étale)` the canonical comparison
`RΓ(X_étale, K) ⟶ RΓ(U_étale, a⁻¹ K)` is an isomorphism. Here `a : Sh(U_étale) ⟶ Sh(X_étale)`
is the Section 85.32 spaces-étale augmentation. -/
@[stacks 0DH8]
theorem rGammaInverseImageComparison_app_isIso (ha : IsFppfHypercovering a)
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIso ((rGammaInverseImageComparison a).app K) :=
  sorry

/-- The comparison `RΓ(X_étale, -) ⟶ a⁻¹ ⋙ RΓ(U_étale, -)` is an isomorphism of functors
on `D⁺(X_étale)`. -/
theorem rGammaInverseImageComparison_isIso (ha : IsFppfHypercovering a) :
    IsIso (rGammaInverseImageComparison a) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
