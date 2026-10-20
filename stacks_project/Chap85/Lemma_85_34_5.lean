/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_34_5_Comparison

/-!
# Lemma 85.34.5

Let `S` be a scheme, `X` an algebraic space over `S`, and `U` a simplicial
algebraic space over `S`, with augmentation `a : U ⟶ X`. If `a` is an fppf
hypercovering of `X`, then for every `K` in `D_QCoh(𝒪_X)` the canonical
comparison `RΓ(X_étale, K) ⟶ RΓ(U_étale, a^* K)` is an isomorphism, where
`a : Sh(U_étale) ⟶ Sh(X_étale)` is the Section 85.32 spaces-étale augmentation.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Lemma 85.34.5: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `U` be a simplicial algebraic space over `S`. Let `a : U ⟶ X` be an
augmentation. If `a : U ⟶ X` is an fppf hypercovering of `X`, then
`RΓ(X_étale, K) ⟶ RΓ(U_étale, a^* K)` is an isomorphism for
`K ∈ D_QCoh(𝒪_X)`. Here `a : Sh(U_étale) ⟶ Sh(X_étale)` is the Section 85.32
spaces-étale augmentation `spacesEtaleAugmentationHom`. -/
@[stacks 0DHG]
theorem rGammaPullbackComparison_app_isIso (ha : IsFppfHypercovering a)
    (K : spacesDerivedQCoh X) :
    IsIso ((rGammaPullbackComparison a).app K.obj) :=
  sorry

/-- The comparison `RΓ(X_étale, -) ⟶ a^* ⋙ RΓ(U_étale, -)` is an isomorphism at
every object of `D_QCoh(𝒪_X)`. -/
theorem rGammaPullbackComparison_isIso (ha : IsFppfHypercovering a) :
    ∀ K : spacesDerivedQCoh X, IsIso ((rGammaPullbackComparison a).app K.obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
