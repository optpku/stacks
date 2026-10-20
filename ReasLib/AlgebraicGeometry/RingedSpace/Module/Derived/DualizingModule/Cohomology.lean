/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.DualizingModule

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingModule

/-- Regard a dualizing module as an object of the category of coherent modules. -/
def toCoh {X : RingedSpace.{u}} {K : ModuleDerived X}
    [MonoidalCategory (ModuleDerived X)] {H : MonoidalClosed (ModuleDerived X)}
    {n : ℤ} {M : X.Modules} (hω : IsDualizingModule K H n M) : RingedSpace.Coh X :=
  ⟨M, hω.coherent⟩

/-- The underlying module of the coherent object associated to a dualizing module is the
original dualizing module. -/
theorem toCoh_obj {X : RingedSpace.{u}} {K : ModuleDerived X}
    [MonoidalCategory (ModuleDerived X)] {H : MonoidalClosed (ModuleDerived X)}
    {n : ℤ} {M : X.Modules} (hω : IsDualizingModule K H n M) :
    hω.toCoh.obj = M := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingModule
