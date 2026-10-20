module

public import ReasLib.AlgebraicGeometry.ChowGroup.MilnorComplex

open AlgebraicGeometry CategoryTheory

universe u

/- Compatibility bridge for the pointwise locally finite Milnor complex. -/
#check (AlgebraicGeometry.ChowGroup.Pointwise.milnorComplex :
  ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) [IsDimensionFunction d] (k : ℤ), ShortComplex Ab)
