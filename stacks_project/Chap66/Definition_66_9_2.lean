/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Definition_66_9_2_Dimension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/- Definition 66.9.2: for a scheme `S` and an algebraic space `X` over `S`, the dimension
`dimension X` is the supremum of the étale-local dimensions `dimensionAt x` as `x` runs over
`Points X`. This is not the topological Krull dimension of `|X|`. -/
@[stacks 04N6] #check (AlgebraicGeometry.AlgebraicSpace.dimension X : WithBot ℕ∞)
