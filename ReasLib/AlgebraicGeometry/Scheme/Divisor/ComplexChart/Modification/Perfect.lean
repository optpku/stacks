module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ideal.Eta.Derived.Perfect
import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.IdealSheaf

universe u

namespace AlgebraicGeometry.Scheme.IsGoodTripleModification

/-- Derived ideal-sheaf eta sends the derived pullback of a perfect module along a
good-triple modification to a perfect object. -/
@[stacks 0F8U]
theorem etaPullback_isPerfect {X X' : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (b : X' ⟶ X)
    [IsGoodTripleModification D M b] :
    RingedSpace.ModuleDerived.IsPerfect
      ((Eta.Derived.functor (D.comap b).toSubobject).obj
        ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M)) := sorry

end AlgebraicGeometry.Scheme.IsGoodTripleModification
