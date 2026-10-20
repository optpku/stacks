/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectTensorComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Pullback
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Inverse
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit

/-!
# Actual tensor and unit comparisons for module pullback

The forward tensor comparison is the existing adjunct of the direct-image
tensor map. Its reverse uses the actual section fibers of that specified map.
Unit comparisons retain the original structure-ring presentation and the
canonical monoidal transport.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.PullbackTensor

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The specified adjoint-transpose tensor comparison is bijective on sections. -/
theorem comparison_bijective (M N : Y.Modules) (U : (smallEtaleSite X)ᵒᵖ) :
    Function.Bijective ((DirectTensorComparison.pullbackTensor f M N).val.app U).hom := sorry

/-- The pullback tensor isomorphism retains the original forward comparison and
uses its actual section fibers for the reverse map. -/
def tensorIso (M N : Y.Modules) :
    (pullback f).obj (M ⊗ N) ≅ (pullback f).obj M ⊗ (pullback f).obj N :=
  SheafOfModules.isoOfBijective (DirectTensorComparison.pullbackTensor f M N)
    (comparison_bijective f M N)

@[simp]
theorem tensorIso_hom (M N : Y.Modules) :
    (tensorIso f M N).hom = DirectTensorComparison.pullbackTensor f M N := rfl

/-- The reverse tensor comparison acts by the specified actual section preimage. -/
@[simp]
theorem tensorIso_inv_app (M N : Y.Modules) (U : (smallEtaleSite X)ᵒᵖ)
    (s : (((pullback f).obj M ⊗ (pullback f).obj N).val.obj U)) :
    ((tensorIso f M N).inv.val.app U).hom s =
      SheafOfModules.sectionPreimage (DirectTensorComparison.pullbackTensor f M N) U s := rfl

/-- The tensor comparison is natural in the two module arguments. -/
theorem tensorIso_naturality {M M' N N' : Y.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    (pullback f).map (a ⊗ₘ b) ≫ (tensorIso f M' N').hom =
      (tensorIso f M N).hom ≫ ((pullback f).map a ⊗ₘ (pullback f).map b) := sorry

/-- Restriction along the genuine structure-ring isomorphism identifies its unit modules. -/
def structureUnitCommIso (Z : AlgebraicSpace S) :
    SheafOfModules.unit (structureSheaf Z) ≅
      (ofCommModules Z).obj (SheafOfModules.unit (commRingSheaf Z)) where
  hom :=
    { val :=
        { app := fun U ↦
            let M := (SheafOfModules.unit (structureSheaf Z)).val.obj U
            let N := ((ofCommModules Z).obj (SheafOfModules.unit (commRingSheaf Z))).val.obj U
            letI : Module ((structureSheaf Z).obj.obj U) M := M.isModule
            letI : Module ((structureSheaf Z).obj.obj U) N := N.isModule
            ConcreteCategory.ofHom (C := ModuleCat ((structureSheaf Z).obj.obj U))
              (X := M) (Y := N) (show M →ₗ[(structureSheaf Z).obj.obj U] N from
                { toFun := fun x ↦ (commRingSheafIso Z).inv.hom.app U x
                  map_add' := sorry
                  map_smul' := sorry })
          naturality := sorry } }
  inv :=
    { val :=
        { app := fun U ↦
            let M := (SheafOfModules.unit (structureSheaf Z)).val.obj U
            let N := ((ofCommModules Z).obj (SheafOfModules.unit (commRingSheaf Z))).val.obj U
            letI : Module ((structureSheaf Z).obj.obj U) M := M.isModule
            letI : Module ((structureSheaf Z).obj.obj U) N := N.isModule
            ConcreteCategory.ofHom (C := ModuleCat ((structureSheaf Z).obj.obj U))
              (X := N) (Y := M) (show N →ₗ[(structureSheaf Z).obj.obj U] M from
                { toFun := fun x ↦ (commRingSheafIso Z).hom.hom.app U x
                  map_add' := sorry
                  map_smul' := sorry })
          naturality := sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The structure module compares with the actual transported tensor unit. -/
def structureUnitIso (Z : AlgebraicSpace S) :
    SheafOfModules.unit (structureSheaf Z) ≅ 𝟙_ Z.Modules := by
  letI : (ofCommModules Z).Monoidal :=
    inferInstanceAs ((Monoidal.equivalenceTransported (commModulesEquivalence Z)).functor.Monoidal)
  exact structureUnitCommIso Z ≪≫
    (ofCommModules Z).mapIso
      (SheafOfModules.RingedSite.unitIsoTensorUnit (𝒪 := commStructureSheaf Z)) ≪≫
    (Functor.Monoidal.εIso (ofCommModules Z)).symm

/-- Pullback of the structure module has the specified unit comparison. -/
theorem structureUnitComparison_bijective (U : (smallEtaleSite X)ᵒᵖ) :
    Function.Bijective ((IdealSubobject.pullbackUnit f).val.app U).hom := sorry

/-- The structure-module pullback comparison, with its actual section reverse. -/
def structureUnitPullbackIso :
    (pullback f).obj (SheafOfModules.unit (structureSheaf Y)) ≅
      SheafOfModules.unit (structureSheaf X) :=
  SheafOfModules.isoOfBijective (IdealSubobject.pullbackUnit f)
    (structureUnitComparison_bijective f)

/-- The actual tensor-unit comparison combines the existing presentation maps. -/
def unitIso : (pullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules :=
  (pullback f).mapIso (structureUnitIso Y).symm ≪≫
    structureUnitPullbackIso f ≪≫ structureUnitIso X

end AlgebraicGeometry.AlgebraicSpace.Modules.PullbackTensor
