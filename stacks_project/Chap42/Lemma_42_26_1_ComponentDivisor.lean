module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.Divisor

@[expose] public section

#check (AlgebraicGeometry.CycleGroup.flatDivisorDegree :
  ∀ (n : ℤ) (r : ℕ), (n - 1) + (r : ℤ) = n + (r : ℤ) - 1)
