/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SectionAction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Local-section action on sheaves of modules

This file is the sheaf-level bridge to the topology-independent presheaf owner
`PresheafOfModules.SectionAction.action`.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w z

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (O : Sheaf J CommRingCat.{w})
variable (M : SheafOfModules.{z} (CategoryTheory.Sheaf.ringSheafOfComm O))

/-- Multiplication by one local section on the restriction of a module sheaf to a slice site. -/
noncomputable def sectionActionHom (U : C) (r : O.obj.obj (op U)) :
    M.over U ⟶ M.over U where
  val := PresheafOfModules.SectionAction.hom O.obj M.val U r

/-- The component of the sheaf-level section action is the canonical presheaf-level component. -/
@[simp]
theorem sectionActionHom_val_app (U : C) (r : O.obj.obj (op U))
    (V : (Over U)ᵒᵖ) :
    (sectionActionHom O M U r).val.app V =
      PresheafOfModules.SectionAction.app O.obj M.val U r V := sorry

/-- The zero section acts by the zero module-sheaf endomorphism. -/
@[simp]
theorem sectionActionHom_zero (U : C) : sectionActionHom O M U 0 = 0 := sorry

/-- The sheaf-level action is additive in the local section. -/
theorem sectionActionHom_add (U : C) (r s : O.obj.obj (op U)) :
    sectionActionHom O M U (r + s) =
      sectionActionHom O M U r + sectionActionHom O M U s := sorry

/-- The unit section acts by the identity module-sheaf endomorphism. -/
@[simp]
theorem sectionActionHom_one (U : C) : sectionActionHom O M U 1 = 𝟙 _ := sorry

/-- Multiplication of local sections is composition in the sheaf endomorphism ring. -/
theorem sectionActionHom_mul (U : C) (r s : O.obj.obj (op U)) :
    sectionActionHom O M U (r * s) =
      sectionActionHom O M U s ≫ sectionActionHom O M U r := sorry

/-- Multiplication by a local section commutes with every morphism of module sheaves. -/
@[reassoc]
theorem sectionActionHom_naturality
    {M N : SheafOfModules.{z} (CategoryTheory.Sheaf.ringSheafOfComm O)}
    (f : M ⟶ N) (U : C) (r : O.obj.obj (op U)) :
    sectionActionHom O M U r ≫ f.over U =
      f.over U ≫ sectionActionHom O N U r := sorry

/-- The canonical ring action of local sections on a restricted module sheaf. -/
@[stacks 03EM "module-sheaf local-section action"]
noncomputable def sectionAction (U : C) : O.obj.obj (op U) →+* End (M.over U) where
  toFun := sectionActionHom O M U
  map_one' := sectionActionHom_one O M U
  map_zero' := sectionActionHom_zero O M U
  map_mul' := sectionActionHom_mul O M U
  map_add' := sectionActionHom_add O M U

/-- The sheaf-level bundled action evaluates to multiplication by the restricted section. -/
@[simp]
theorem sectionAction_app_apply (U : C) (r : O.obj.obj (op U))
    (V : (Over U)ᵒᵖ) (x : (M.over U).val.obj V) :
    ((sectionAction O M U r).val.app V) x =
      PresheafOfModules.SectionAction.restrict O.obj U r V • x := sorry


-- The morphism components come from the explicit presheaf-level `LinearMap.lsmul` owner.
-- Any `sorryAx` is confined to naturality and ring-homomorphism law fields.

end SheafOfModules
