module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Representative.LocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ideal.Eta.Derived.Perfect
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.IdealSheaf.Eta.Derived

universe u

namespace AlgebraicGeometry.Scheme.IsGoodTriple

/-- Derived ideal-sheaf eta preserves the existence of a global locally bounded finite locally
free representative for a perfect derived module in a good triple. -/
@[stacks 0GTX]
theorem existsEtaRepresentative {X : Scheme.{u}}
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (hgood : IsGoodTriple D M)
    (hrep : RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative M) :
    RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
      ((functor D.toSubobject).obj M) := sorry

end AlgebraicGeometry.Scheme.IsGoodTriple
