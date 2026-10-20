module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Representative.LocallyFree.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ideal.Eta.Derived.LocallyFree
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally free representatives after a good-triple modification

This file records preservation of locally bounded finite locally free representatives after
derived pullback along a good-triple modification and derived ideal-sheaf eta.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.IdealSheaf

universe u

namespace AlgebraicGeometry.Scheme.IsGoodTripleModification

/-- Derived ideal-sheaf eta applied to the derived pullback along a good-triple modification
admits a locally bounded finite locally free representative whenever the original module does. -/
@[stacks 0GU0]
theorem etaPullback_hasLocallyBoundedFiniteLocallyFreeRepresentative
    {X X' : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (b : X' ⟶ X)
    [IsGoodTripleModification D M b]
    (hrep : RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative M) :
    RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
      ((Eta.Derived.functor (D.comap b).toSubobject).obj
        ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M)) := sorry

end AlgebraicGeometry.Scheme.IsGoodTripleModification
