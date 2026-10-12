/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_36_2_Hypercovering
public import stacks_project.Chap85.Lemma_85_33_3_Adjunction

/-!
# Lemma 85.36.3

If `a : U ⟶ X` is a proper hypercovering of an algebraic space `X` over a scheme `S`,
then for every `K` in `D⁺(X_étale)` the canonical derived unit `K ⟶ Ra_*(a⁻¹ K)` is an
isomorphism, where `a` is the Section 85.32 spaces-étale augmentation.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Lemma 85.36.3. Let `S` be a scheme, `X` an algebraic space over `S`, `U` a
simplicial algebraic space over `S`, and `a : U ⟶ X` a proper hypercovering of
`X`. Then for `K` in `D⁺(X_étale)` the canonical derived unit
`K ⟶ Ra_*(a⁻¹ K)` is an isomorphism. Here `a : Sh(U_étale) ⟶ Sh(X_étale)` is the
Section 85.32 spaces-étale augmentation, and the map is `(plusDerivedUnit a).app K`. -/
@[stacks 0DHL]
theorem properPlusDerivedUnit_app_isIso (ha : IsProperHypercovering a)
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIso ((plusDerivedUnit a).app K) :=
  sorry

/-- The derived unit `𝟭 ⟶ plusInverseImage a ⋙ plusDirectImage a` is an isomorphism
when `a` is a proper hypercovering. -/
theorem properPlusDerivedUnit_isIso (ha : IsProperHypercovering a) :
    IsIso (plusDerivedUnit a) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
