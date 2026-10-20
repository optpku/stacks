module

public import ReasLib.AlgebraicGeometry.Scheme.Distance

@[expose] public section

#check (AlgebraicGeometry.Scheme.distanceTo :
  (Y : AlgebraicGeometry.Scheme) → [AlgebraicGeometry.IsNoetherian Y] →
    TopologicalSpace.Closeds Y → Y → ℕ∞)
