/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_33_4_Comparison
public import stacks_project.Chap85.Lemma_85_36_2_Hypercovering

/-!
# Lemma 85.36.4

If `a : U ⟶ X` is a proper hypercovering of an algebraic space `X` over a scheme `S`,
then for every `K` in `D⁺(X_étale)` the canonical comparison
`RΓ(X_étale, K) ⟶ RΓ(U_étale, a⁻¹ K)` is an isomorphism, where `a` is the
Section 85.32 spaces-étale augmentation.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Lemma 85.36.4. Let `S` be a scheme, `X` an algebraic space over `S`, `U` a
simplicial algebraic space over `S`, and `a : U ⟶ X` a proper hypercovering of
`X`. Then for `K` in `D⁺(X_étale)` the canonical comparison
`RΓ(X_étale, K) ⟶ RΓ(U_étale, a⁻¹ K)` is an isomorphism. Here
`a : Sh(U_étale) ⟶ Sh(X_étale)` is the Section 85.32 spaces-étale augmentation,
and the map is `(rGammaInverseImageComparison a).app K`. -/
@[stacks 0DHM]
theorem properPlusRGammaInverseImageComparison_app_isIso
    (ha : IsProperHypercovering a)
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIso ((rGammaInverseImageComparison a).app K) :=
  sorry

/-- The comparison `RΓ(X_étale, -) ⟶ a⁻¹ ⋙ RΓ(U_étale, -)` is an isomorphism of
functors on `D⁺(X_étale)` when `a` is a proper hypercovering. -/
theorem properPlusRGammaInverseImageComparison_isIso (ha : IsProperHypercovering a) :
    IsIso (rGammaInverseImageComparison a) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
