/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.RingTheory.RingHom.Perfect.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a closed immersion locally induced by perfect ring maps, the direct image of the
structure sheaf, placed in degree zero, is a perfect derived module on the target. -/
theorem pushforwardStructureSheaf_isPerfect
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (h_perfect : LocallyOfType RingHom.IsPerfectRingMap i) :
    RingedSpace.ModuleDerived.IsPerfect (pushforwardStructureSheaf i).obj := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
