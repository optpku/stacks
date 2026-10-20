/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Noetherian

/-!
# Points of locally Noetherian algebraic stacks

The points space of a locally Noetherian algebraic stack is locally Noetherian, and it is
Noetherian when the algebraic stack is also quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check
  (AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian.locallyNoetherianSpace :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      [AlgebraicStack.IsLocallyNoetherian X]
      (τ : TopologicalSpace (AlgebraicStack.Points X))
      (_ : AlgebraicStack.IsPointsTopology X τ),
      @TopologicalSpace.LocallyNoetherianSpace (AlgebraicStack.Points X) τ)

#check
  (AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian.noetherianSpace :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      [AlgebraicStack.IsQuasiCompact X] [AlgebraicStack.IsLocallyNoetherian X]
      (τ : TopologicalSpace (AlgebraicStack.Points X))
      (_ : AlgebraicStack.IsPointsTopology X τ),
      @TopologicalSpace.NoetherianSpace (AlgebraicStack.Points X) τ)
