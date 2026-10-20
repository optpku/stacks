/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import stacks_project.Chap103.Lemma_103_8_3_LiftedRestriction

@[expose] public section
open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
open scoped Bicategory
noncomputable section
universe u
namespace AlgebraicGeometry.GroupoidsOver.ModuleUniverseComparison
variable {S : Scheme.{u}}

/-- Restricting the explicitly lifted input along the total functor agrees with
lifting its original inverse image. Both directions preserve the lifted section. -/
def inverseInputIso {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    lift Y ⋙ moduleInverseImageLift f ≅ moduleInverseImage f ⋙ lift X :=
  NatIso.ofComponents (fun M => (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V =>
      { hom := ModuleCat.ofHom
          (X := ((lift Y ⋙ moduleInverseImageLift f).obj M).val.obj V)
          (Y := ((moduleInverseImage f ⋙ lift X).obj M).val.obj V)
          { toFun := fun x => x
            map_add' := by intros; rfl
            map_smul' := by sorry }
        inv := ModuleCat.ofHom
          (X := ((moduleInverseImage f ⋙ lift X).obj M).val.obj V)
          (Y := ((lift Y ⋙ moduleInverseImageLift f).obj M).val.obj V)
          { toFun := fun x => x
            map_add' := by intros; rfl
            map_smul' := by sorry }
        hom_inv_id := by ext x; rfl
        inv_hom_id := by ext x; rfl }) (by intros; ext x; rfl)))
    (by intros; ext V x; rfl)

/-- The input compatibility map is the identity on each actual ULift section. -/
theorem inverseInputIso_hom_section {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (M : etaleModules Y) (V : X.totalᵒᵖ) (s : M.val.obj ((toFunctor f).op.obj V)) :
    ((inverseInputIso f).hom.app M).val.app V (ULift.up s) = ULift.up s := rfl

/-- The scheme chart actually used by restriction at the original object y. -/
abbrev chart {Y : GroupoidsOver S} (y : Y.total) (W : (Y.p.obj y).left.Etale) : Y.total :=
  (toFunctor (moduleSliceHom y)).obj
    ((smallEtaleFunctor _ _ (AlgebraicSpace.ofOverSliceEquiv (Y.p.obj y))).obj
      ((AlgebraicSpace.schemeEtaleRingedHom (Y.p.obj y)).base.obj W))

/-- The scheme restriction evaluates on the original chart, without a small/BIG
equivalence or any choice of a smaller representative. -/
theorem restriction_carrier {Y : GroupoidsOver S} (y : Y.total)
    (M : EtaleModulesLift Y) (W : (Y.p.obj y).left.Etale) :
    (((moduleAtObjectLift y ⋙ modulesToSchemeLift (Y.p.obj y)).obj M).val.obj (op W) :
        Type (u + 1)) = M.val.obj (op (chart y W)) := rfl

/-- For an original input the same chart has literally its ULift section carrier. -/
theorem original_restriction_carrier {Y : GroupoidsOver S} (y : Y.total)
    (M : etaleModules Y) (W : (Y.p.obj y).left.Etale) :
    (((moduleAtObjectLift y ⋙ modulesToSchemeLift (Y.p.obj y)).obj ((lift Y).obj M)).val.obj
        (op W) : Type (u + 1)) = ULift.{u + 1} (M.val.obj (op (chart y W))) := rfl

end AlgebraicGeometry.GroupoidsOver.ModuleUniverseComparison
