/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.LinearSeries

universe u

open TopologicalSpace

#check (AlgebraicGeometry.LinearSeries : ∀ {k : Type u} [Field k]
  (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.IsProper X.hom],
  (topologicalKrullDim X.left ≤ 1) → ℕ → ℕ → Type (u + 1))
