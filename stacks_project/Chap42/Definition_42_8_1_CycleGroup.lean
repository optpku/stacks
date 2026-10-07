module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Dimension

open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicCycle.dimensionSubgroup :
  {X : Scheme.{u}} → (X → ℤ) → ℤ → AddSubgroup (AlgebraicGeometry.AlgebraicCycle X ℤ))
