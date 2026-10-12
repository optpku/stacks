/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Coproduct
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.CategoryTheory.Preadditive.CompactObject
public import Mathlib.Topology.QuasiSeparated

/-!
# Compact and perfect quasicoherent complexes

Compact objects in the derived category of quasicoherent modules on a
quasi-compact and quasi-separated scheme are characterized by perfectness.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- An object of the derived category of quasicoherent modules on a quasi-compact and
quasi-separated scheme is compact if and only if its underlying derived module is perfect. -/
theorem isCompactObject_iff_isPerfect {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X]
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) :
    IsCompactObject E ↔ RingedSpace.ModuleDerived.IsPerfect E.obj := sorry

/-- A perfect object of the derived category of quasicoherent modules on a quasi-compact and
quasi-separated scheme is compact. -/
theorem isCompactObject_of_isPerfect {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X]
    {E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)}
    (hE : RingedSpace.ModuleDerived.IsPerfect E.obj) : IsCompactObject E := sorry

/-- A compact object of the derived category of quasicoherent modules on a quasi-compact and
quasi-separated scheme has a perfect underlying derived module. -/
theorem isPerfect_of_isCompactObject {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X]
    {E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)}
    (hE : IsCompactObject E) : RingedSpace.ModuleDerived.IsPerfect E.obj := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
