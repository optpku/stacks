module

public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.RingTheory.Gorenstein.Regular

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Every regular scheme is Gorenstein. -/
instance instGorensteinOfRegular (X : Scheme.{u}) [Regular X] : Gorenstein X := sorry

end AlgebraicGeometry.Scheme
