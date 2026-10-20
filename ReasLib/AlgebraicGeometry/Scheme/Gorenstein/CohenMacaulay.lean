module

public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import ReasLib.RingTheory.Gorenstein.CohenMacaulay

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Gorenstein

/-- Every Gorenstein scheme is Cohen-Macaulay. -/
instance instCohenMacaulay (X : Scheme.{u}) [Gorenstein X] : CohenMacaulay X := sorry

end AlgebraicGeometry.Scheme.Gorenstein
