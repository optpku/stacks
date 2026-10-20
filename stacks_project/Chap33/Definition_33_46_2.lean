/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.EmbeddingDimension
import StacksCheckRecall

@[expose] public section

/-!
# Definition 33.46.2 compatibility entry point

The reusable relative tangent-space formulation of embedding dimension is owned by
`ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.EmbeddingDimension`.
-/

universe u

variable {k : Type u} [Field k]
variable (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.LocallyAlgebraic X]
variable (x : X.left)

/- Definition 33.46.2: the embedding dimension of `X/k` at `x` is the
`κ(x)`-dimension of the relative tangent space `T_{X/k,x}`. -/
@[stacks 0C2H] #check (AlgebraicGeometry.Scheme.Hom.tangentDimensionAt X.hom x : ℕ)
