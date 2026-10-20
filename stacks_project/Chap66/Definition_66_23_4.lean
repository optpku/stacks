/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricBranch
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 66.23.4: for a scheme `S`, an algebraic space `X` over `S`, and a point
`x ∈ |X|`, the number of geometric branches of `X` at `x` is `n` when the equivalent
conditions of Lemma 66.23.3 hold, and `⊤` otherwise. -/
@[stacks 0DQ4] #check
  (AlgebraicGeometry.AlgebraicSpace.geometricBranchNumber :
    {S : AlgebraicGeometry.Scheme.{u}} → (X : AlgebraicGeometry.AlgebraicSpace S) →
      AlgebraicGeometry.AlgebraicSpace.Points X → ℕ∞)
