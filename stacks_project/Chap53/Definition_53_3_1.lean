/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.LinearSeries
import StacksCheckRecall

universe u

open TopologicalSpace

/- Definition 53.3.1: a linear series 𝔤^r_d on a proper scheme `X` over a field consists of
an invertible module of degree `d` and an `(r + 1)`-dimensional subspace of its global sections. -/
@[stacks 0CCN] #check (AlgebraicGeometry.LinearSeries : ∀ {k : Type u} [Field k]
  (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.IsProper X.hom],
  (topologicalKrullDim X.left ≤ 1) → ℕ → ℕ → Type (u + 1))
