/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (X : GroupoidsOver S)
  [AlgebraicStack X] [AlgebraicStack.IsLocallyNoetherian X]

/- Definition 100.12.3: let `S` be a scheme. Let `X` be a locally Noetherian algebraic
stack over `S`. The dimension `dimension X` of `X` is the supremum of the
pointwise dimensions `dimensionAt x` as `x` runs over `|X|`. -/
@[stacks 0AFP] #check (AlgebraicGeometry.AlgebraicStack.dimension X : EInt)
