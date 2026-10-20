/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits TopologicalSpace

universe u

/- Lemma 87.14.4: Completion along the inverse image of a closed subset forms a
cartesian square with the original morphism of algebraic spaces. -/
@[stacks 0APV] #check (AlgebraicGeometry.AlgebraicSpace.completionAlong_isPullback :
  ∀ {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)),
    IsPullback (completionAlong.ι X' (T.preimage (Points.continuous_map f)))
      (completionAlong.map f T) f (completionAlong.ι X T))

#check (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces_completionAlong_map :
  ∀ {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)),
    representableByAlgebraicSpaces (completionAlong.map f T))
