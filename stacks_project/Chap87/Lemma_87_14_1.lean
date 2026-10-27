/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CompletionAlong.McQuillan
import StacksCheckRecall

/-!
# Completion of an affine scheme along a closed subset

The functor of points sending a scheme `U` over `S` to the morphisms
`U ⟶ X` landing in a closed subset `T ⊆ |X|` is a McQuillan affine formal
algebraic space when the underlying scheme of `X` is affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AffineFormalAlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

/- Lemma 87.14.1: Let `S` be a scheme. Let `X` be an affine scheme over `S`.
Let `T ⊆ |X|` be a closed subset. Then the functor `(Sch/S)_fppf → Sets`
sending `U` to `{ f : U ⟶ X | f(|U|) ⊆ T }` is a McQuillan affine formal
algebraic space. -/
@[stacks 0AIY] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.instIsMcQuillanAffine_completionAlong :
    ∀ {S : Scheme.{u}} (X : Over S) [IsAffine X.left] (T : Closeds X.left),
      AlgebraicGeometry.FormalAlgebraicSpace.IsMcQuillanAffine (completionAlong X T))

#check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.isMcQuillanAffine_affineCompletionAlong :
    ∀ {S : Scheme.{u}} {A : Type u} [CommRing A]
      (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A))),
      AlgebraicGeometry.FormalAlgebraicSpace.IsMcQuillanAffine
        (affineCompletionAlong structureHom T))

