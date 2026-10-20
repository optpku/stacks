module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.LogPole
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSpace.DeRham.LogPole

/-- If `X ⟶ T` and the effective Cartier divisor `Y ⟶ T` are smooth, then the de Rham
complex with logarithmic poles along `Y ⊂ X` is defined over `S`. -/
theorem isDefined_of_smooth {S T X Y : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] [Smooth f] [Smooth (i ≫ f)] :
    IsDefined (f ≫ g) i := sorry

end AlgebraicGeometry.RingedSpace.DeRham.LogPole
