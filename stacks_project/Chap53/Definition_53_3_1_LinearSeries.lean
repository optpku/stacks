module

public import ReasLib.AlgebraicGeometry.Scheme.LinearSeries

universe u

open TopologicalSpace

#check (AlgebraicGeometry.LinearSeries : ∀ {k : Type u} [Field k]
  (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.IsProper X.hom],
  (topologicalKrullDim X.left ≤ 1) → ℕ → ℕ → Type (u + 1))
