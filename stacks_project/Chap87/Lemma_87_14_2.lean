/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Types
import StacksCheckRecall

/-!
# Completion of an algebraic space along a closed subset

The functor of points sending a scheme `U` over `S` to the morphisms
`U ⟶ X` landing in a closed subset `T ⊆ Points X` is a formal algebraic
space.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

/- Lemma 87.14.2: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `T ⊆ |X|` be a closed subset. Then the functor `(Sch/S)_fppf → Sets`
sending `U` to `{ f : U ⟶ X | f(|U|) ⊆ T }` is a formal algebraic space. -/
@[stacks 0AIZ] #check
  (AlgebraicGeometry.AlgebraicSpace.instIsFormalAlgebraicSpace_completionAlong :
    {S : Scheme.{u}} → (X : AlgebraicSpace S) →
      (T : Closeds (AlgebraicGeometry.AlgebraicSpace.Points X)) →
      AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace
        (AlgebraicGeometry.AlgebraicSpace.completionAlong X T))
