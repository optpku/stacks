module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein.CohenMacaulay

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Gorenstein

/-- A Gorenstein scheme morphism is Cohen--Macaulay. -/
instance instCohenMacaulay {X Y : Scheme.{u}} (f : X ⟶ Y) [Gorenstein f] :
    CohenMacaulay f := sorry

end AlgebraicGeometry.Gorenstein
