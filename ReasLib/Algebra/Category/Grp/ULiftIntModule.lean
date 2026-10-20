/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AddCommGrpCat

/-- The coefficient functor sending an abelian group to the associated
`ULift ℤ`-module. -/
def toULiftIntModule :
    AddCommGrpCat.{u} ⥤ ModuleCat.{u} (ULift.{u} ℤ) :=
  (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom

/-- Conversion to lifted-integer modules is integer-module conversion followed by restriction of scalars. -/
theorem toULiftIntModule_eq :
    toULiftIntModule =
      (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv ⋙
        ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom :=
  sorry

/-- The canonical additive map from an abelian group to the associated
`ULift ℤ`-module, via the inverse of `forget₂`. -/
def toULiftIntModuleAddHom (A : AddCommGrpCat.{u}) :
    A →+ toULiftIntModule.obj A :=
  ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.counitIso.inv.app A).hom

/-- The additive coefficient map is the inverse counit of the integer-module equivalence. -/
theorem toULiftIntModuleAddHom_eq (A : AddCommGrpCat.{u}) :
    toULiftIntModuleAddHom A =
      ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.counitIso.inv.app A).hom :=
  sorry

end AddCommGrpCat

end
