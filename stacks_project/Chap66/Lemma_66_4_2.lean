/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 66.4.2: let `S` be a scheme and let `X` be a scheme over `S`. The points of `X`
as a scheme are in canonical 1-1 correspondence with the points of `X` as an algebraic
space. -/
@[stacks 03BV] #check (AlgebraicGeometry.AlgebraicSpace.ofOver.pointsEquiv :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : CategoryTheory.Over S),
    X.left ≃ AlgebraicGeometry.AlgebraicSpace.Points
      (AlgebraicGeometry.AlgebraicSpace.ofOver X))
