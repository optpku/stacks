/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Pullback

/-! # Pullback of compatible module sections on algebraic spaces -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- The type-valued sheaf underlying the structure module of an algebraic space. -/
def unitCarrierIso (X : AlgebraicSpace S) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj
      (SheafOfModules.unit (structureSheaf X)) ≅
      (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj (structureSheaf X) where
  hom := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  inv := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The type-valued sheaf underlying the unit of `f⁻¹ 𝒪_Y`. -/
def inverseImageUnitCarrierIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (Sheaf.InternalModule.ToInternal.underlying
          ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y))).obj
      (SheafOfModules.unit
        ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y))) ≅
      (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj
        ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y)) where
  hom := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  inv := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Inverse image of the structure module of `Y` is the unit module of `f⁻¹ 𝒪_Y`. -/
def moduleInverseImageUnitIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ((ringedToposHom f).toTopos.moduleInverseImage (structureSheaf Y)).obj
        (SheafOfModules.unit (structureSheaf Y)) ≅
      SheafOfModules.unit
        ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y)) where
  hom :=
    Sheaf.InternalModule.homOfUnderlying
      ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y))
      (((ringedToposHom f).toTopos.moduleInverseImageForgetIso (structureSheaf Y)).hom.app
          (SheafOfModules.unit (structureSheaf Y)) ≫
        (ringedToposHom f).toTopos.inverseImage.map (unitCarrierIso Y).hom ≫
        (ringedToposHom f).toTopos.ringInverseImageForgetIso.inv.app (structureSheaf Y) ≫
        (inverseImageUnitCarrierIso f).inv)
      sorry sorry
  inv :=
    Sheaf.InternalModule.homOfUnderlying
      ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y))
      ((inverseImageUnitCarrierIso f).hom ≫
        (ringedToposHom f).toTopos.ringInverseImageForgetIso.hom.app (structureSheaf Y) ≫
        (ringedToposHom f).toTopos.inverseImage.map (unitCarrierIso Y).inv ≫
        ((ringedToposHom f).toTopos.moduleInverseImageForgetIso (structureSheaf Y)).inv.app
          (SheafOfModules.unit (structureSheaf Y)))
      sorry sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The free rank-one module `𝒪_X` maps to the scalar extension of `f⁻¹ 𝒪_Y`. -/
def extendScalarsUnitFromStructure {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    SheafOfModules.unit (structureSheaf X) ⟶
      (SheafOfModules.ChangeOfRings.extendScalars (ringedToposHom f).structureMap).obj
        (SheafOfModules.unit
          ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y))) :=
  let α := (ringedToposHom f).structureMap
  let Rinv := (ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y)
  let M := (SheafOfModules.ChangeOfRings.extendScalars α).obj (SheafOfModules.unit Rinv)
  let s :=
    ((SheafOfModules.restrictScalars α).obj M).unitHomEquiv
      ((SheafOfModules.ChangeOfRings.extendRestrictAdjunction α).unit.app
        (SheafOfModules.unit Rinv))
  M.unitHomEquiv.symm (PresheafOfModules.sectionsMk (fun U ↦ s.val U) fun _ _ h ↦ s.property h)

/-- The canonical map `𝒪_X ⟶ f^* 𝒪_Y`. -/
def structureModulePullbackInv {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    SheafOfModules.unit (structureSheaf X) ⟶
      (pullback f).obj (SheafOfModules.unit (structureSheaf Y)) :=
  extendScalarsUnitFromStructure f ≫
    (SheafOfModules.ChangeOfRings.extendScalars (ringedToposHom f).structureMap).map
      (moduleInverseImageUnitIso f).inv ≫
    (pullbackIsoTopos f).inv.app (SheafOfModules.unit (structureSheaf Y))

/-- The canonical identification `𝒪_X ≅ f^* 𝒪_Y` of structure modules. -/
def structureModulePullbackIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    SheafOfModules.unit (structureSheaf X) ≅
      (pullback f).obj (SheafOfModules.unit (structureSheaf Y)) where
  hom := structureModulePullbackInv f
  inv := IdealSubobject.pullbackUnit f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Pullback of a compatible section along a morphism of algebraic spaces. -/
def sectionsPullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : Y.Modules)
    (s : F.sections) : ((pullback f).obj F).sections :=
  SheafOfModules.sectionsMap
    ((pullback f).map ((SheafOfModules.unitHomEquiv F).symm s))
    (SheafOfModules.unitHomEquiv ((pullback f).obj (SheafOfModules.unit (structureSheaf Y)))
      (structureModulePullbackInv f))

end AlgebraicGeometry.AlgebraicSpace.Modules
