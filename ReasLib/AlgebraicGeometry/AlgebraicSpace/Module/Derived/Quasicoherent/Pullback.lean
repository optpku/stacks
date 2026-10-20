/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pullback.Preservation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Shift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-! # Pullback of derived quasi-coherent modules on algebraic spaces -/

@[expose] public section
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The actual unbounded derived pullback restricted to quasi-coherent cohomology. -/
def pullback (f : Y ⟶ X) : DerivedQCoh X ⥤ DerivedQCoh Y :=
  ObjectProperty.FullSubcategory.restrict (ModuleDerived.pullback f)
    (ModuleDerived.pullback_preservesQuasiCoherent f)

/-- Forgetting quasi-coherence retains the canonical cell-model derived pullback. -/
def pullback.cellModelInclusionIso (f : Y ⟶ X) :
    pullback f ⋙ inclusion Y ≅ inclusion X ⋙ ModuleDerived.pullback f :=
  ObjectProperty.FullSubcategory.restrict.compιIso (ModuleDerived.pullback f)
    (ModuleDerived.pullback_preservesQuasiCoherent f)

/-- Forgetting restricted pullback compares with the total left derived presentation. -/
def pullback.inclusionIso (f : Y ⟶ X) :
    pullback f ⋙ inclusion Y ≅
      inclusion X ⋙ Functor.LeftDerived.Homotopy.functor (Modules.pullback f) :=
  pullback.cellModelInclusionIso f ≪≫
    Functor.isoWhiskerLeft (inclusion X) (ModuleDerived.pullbackIsoTotalLeftDerived f)

/-- The underlying object of restricted pullback is the concrete derived pullback. -/
@[simp]
theorem pullback.obj_obj (f : Y ⟶ X) (E : DerivedQCoh X) :
    ((pullback f).obj E).obj = (ModuleDerived.pullback f).obj E.obj := rfl

/-- Restricted pullback inherits the canonical shift of concrete derived pullback. -/
noncomputable instance pullback.commShift (f : Y ⟶ X) : (pullback f).CommShift ℤ :=
  inferInstanceAs (((derivedQuasiCoherentModuleProperty Y).lift
    (inclusion X ⋙ ModuleDerived.pullback f)
    (fun E ↦ ModuleDerived.pullback_preservesQuasiCoherent f E.obj E.property)).CommShift ℤ)

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
