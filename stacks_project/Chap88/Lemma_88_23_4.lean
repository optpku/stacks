/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Proper
import StacksCheckRecall

/-!
# Proper morphisms of completions

If a morphism of algebraic spaces is proper, then the induced morphism of
formal completions along a closed subset is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

/- Lemma 88.23.4: If `f : X' ⟶ X` is proper, then the induced morphism
`completionAlong.map f T` of completions along a closed subset `T` of
`Points X` is proper. -/
@[stacks 0GDD] #check
  (AlgebraicGeometry.AlgebraicSpace.proper_completionAlongMap :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
      [AlgebraicGeometry.AlgebraicSpace.Proper f]
      (T : Closeds (AlgebraicGeometry.AlgebraicSpace.Points X)),
      AlgebraicGeometry.FormalAlgebraicSpace.Proper
        (AlgebraicGeometry.AlgebraicSpace.completionAlong.map f T))
