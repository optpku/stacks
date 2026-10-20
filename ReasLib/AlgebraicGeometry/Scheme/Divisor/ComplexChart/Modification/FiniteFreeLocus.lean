module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Cohomology.FiniteFreeLocus

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IsGoodTripleModification

/-- A good-triple modification is an isomorphism over the maximal open on which all
cohomology sheaves of the perfect derived module are finite locally free. -/
theorem isIsoRestrictFiniteFreeOpen {X X' : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (b : X' ⟶ X)
    [IsGoodTripleModification D M b] :
    IsIso (b ∣_ hM.finiteFreeOpen (fun x ↦ inferInstance)) := sorry

end AlgebraicGeometry.Scheme.IsGoodTripleModification
