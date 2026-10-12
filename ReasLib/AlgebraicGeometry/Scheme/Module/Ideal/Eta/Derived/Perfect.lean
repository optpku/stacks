/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ideal.Eta.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.IdealSheaf.Eta.Derived

universe u

namespace AlgebraicGeometry.Scheme.IsGoodTriple

/-- Derived ideal-sheaf eta preserves perfectness for a perfect module in a good triple. -/
@[stacks 0GTW]
theorem etaIsPerfect {X : Scheme.{u}}
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (hgood : IsGoodTriple D M) :
    RingedSpace.ModuleDerived.IsPerfect
      ((functor D.toSubobject).obj M) := sorry

end AlgebraicGeometry.Scheme.IsGoodTriple
