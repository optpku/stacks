/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

@[expose] public section
open CategoryTheory Opposite
noncomputable section
universe u v w v' w'
namespace SheafOfModules.CoefficientEquivalence
variable {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (e : C ≌ D)
variable [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
variable {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
variable (φ : S ≅ (e.functor.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- The reverse coefficient morphism is restriction along the actual counit
followed by the supplied coefficient inverse. -/
def reverse : R ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{u} K J).obj S :=
  ObjectProperty.homMk
    (Functor.whiskerRight (NatTrans.op e.counit) R.obj ≫
      e.inverse.op.whiskerLeft φ.inv.hom)

set_option backward.isDefEq.respectTransparency false in
/-- The first coefficient triangle is the supplied ring isomorphism's inverse law. -/
theorem first : Functor.whiskerRight (NatTrans.op e.counit) R.obj =
    (reverse e φ).hom ≫ e.inverse.op.whiskerLeft φ.hom.hom := by
  let iso : S.obj ≅ e.functor.op ⋙ R.obj := (sheafToPresheaf J RingCat.{u}).mapIso φ
  apply NatTrans.ext
  funext U
  change R.obj.map (e.counit.app U.unop).op =
    (R.obj.map (e.counit.app U.unop).op ≫ iso.inv.app (e.inverse.op.obj U)) ≫
      iso.hom.app (e.inverse.op.obj U)
  rw [Category.assoc, iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The second coefficient triangle combines naturality and the actual
unit/counit triangle of e. It asserts an equation of the displayed maps. -/
theorem second : φ.hom.hom ≫ e.functor.op.whiskerLeft (reverse e φ).hom ≫
    Functor.whiskerRight (NatTrans.op e.unit) S.obj = 𝟙 S.obj := by
  let iso : S.obj ≅ e.functor.op ⋙ R.obj := (sheafToPresheaf J RingCat.{u}).mapIso φ
  apply NatTrans.ext
  funext U
  change iso.hom.app U ≫ (R.obj.map (e.counit.app (e.functor.obj U.unop)).op ≫
    iso.inv.app (e.functor.op ⋙ e.inverse.op |>.obj U)) ≫
    S.obj.map (e.unit.app U.unop).op = 𝟙 _
  simp only [Category.assoc]
  erw [← iso.inv.naturality (e.unit.app U.unop).op]
  change iso.hom.app U ≫ R.obj.map (e.counit.app (e.functor.obj U.unop)).op ≫
    R.obj.map (e.functor.map (e.unit.app U.unop)).op ≫ iso.inv.app U = 𝟙 _
  rw [← Category.assoc (R.obj.map _), ← R.obj.map_comp, ← op_comp]
  erw [e.functor_unit_comp]
  change iso.hom.app U ≫ R.obj.map (𝟙 (e.functor.op.obj U)) ≫ iso.inv.app U = 𝟙 _
  rw [R.obj.map_id]
  erw [Category.id_comp]
  exact iso.hom_inv_id_app U

/-- Both module functors are explicit pushforwards along the two site functors. -/
def equivalence : SheafOfModules.{u} R ≌ SheafOfModules.{u} S :=
  SheafOfModules.pushforwardPushforwardEquivalence e φ.hom (reverse e φ)
    (first e φ) (second e φ)

/-- The inverse pushforward is a specified left adjoint to the original pushforward. -/
def adjunction : SheafOfModules.pushforward.{u} (reverse e φ) ⊣
    SheafOfModules.pushforward.{u} φ.hom :=
  (equivalence e φ).symm.toAdjunction

end SheafOfModules.CoefficientEquivalence
