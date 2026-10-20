/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap87.Lemma_87_14_1_Completion
public import stacks_project.Chap87.Lemma_87_14_1_McQuillan

/-!
# Completion of an affine scheme along a closed subset

The functor of points sending a scheme `U` over `S` to the morphisms
`U ⟶ X` landing in a closed subset `T ⊆ |X|` is a McQuillan affine formal
algebraic space when `X` is affine over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AffineFormalAlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- Lemma 87.14.1: Let `S` be a scheme. Let `X` be an affine scheme over `S`.
Let `T ⊆ |X|` be a closed subset. Then the functor `(Sch/S)_fppf → Sets`
sending `U` to `{ f : U ⟶ X | f(|U|) ⊆ T }` is a McQuillan affine formal
algebraic space. -/
@[stacks 0AIY]
instance instIsMcQuillanAffine_completionAlong {S : Scheme.{u}} (X : Over S)
    [IsAffine X.left] (T : Closeds X.left) :
    IsMcQuillanAffine (completionAlong X T) :=
  sorry

/-- On `X = Spec(A)`, the functor-of-points completion along `T` is a McQuillan
affine formal algebraic space. -/
theorem isMcQuillanAffine_affineCompletionAlong {S : Scheme.{u}} {A : Type u}
    [CommRing A] (structureHom : Spec (.of A) ⟶ S)
    (T : Closeds (Spec (.of A))) :
    IsMcQuillanAffine (affineCompletionAlong structureHom T) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
