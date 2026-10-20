/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.VirtualRank

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ChernClass.Derived

#check (AlgebraicGeometry.ChernClass.Derived.rankClass :
    ∀
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E),
    ChowCohomology.Nonnegative.degree δ π 0)

#check (AlgebraicGeometry.ChernClass.Derived.rankChoose :
    ∀
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (n : ℕ),
    ChowCohomology.Nonnegative.degree δ π 0)

end AlgebraicGeometry.ChernClass.Derived
