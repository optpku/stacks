/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ProjectionFormula
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.StructureModule
public import ReasLib.CategoryTheory.DerivedCategory.Functor.KInjectiveModel
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalHomotopy

/-! # Structure-module projection formula along a closed immersion -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory AlgebraicGeometry ComplexShape

noncomputable section

set_option backward.isDefEq.respectTransparency false
-- The cochain model and its laws remain private implementation details of the public comparison.
set_option backward.privateInPublic true

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.ClosedImmersion

variable {S : Scheme.{u}} {Z Y : AlgebraicSpace S}

private def structureComplex (Z : AlgebraicSpace S) : CochainComplex Z.Modules ℤ :=
  (HomologicalComplex.single Z.Modules (up ℤ) 0).obj
    (SheafOfModules.unit (structureSheaf Z))

private def moduleComparison (i : Z ⟶ Y) (F : Y.Modules) :
    (Modules.pushforward i).obj (SheafOfModules.unit (structureSheaf Z)) ⊗ F ⟶
      (Modules.pushforward i).obj ((Modules.pullback i).obj F) :=
  (Modules.pullbackPushforwardAdjunction i).homEquiv _ _
    (Modules.DirectTensorComparison.pullbackTensor i _ F ≫
      ((Modules.pullbackPushforwardAdjunction i).counit.app
          (SheafOfModules.unit (structureSheaf Z)) ⊗ₘ 𝟙 _) ≫
        ((Modules.structureModuleIsoTensorUnit Z).hom ▷ _) ≫ (λ_ _).hom)

private theorem moduleComparison_naturality (i : Z ⟶ Y)
    {F G : Y.Modules} (a : F ⟶ G) :
    (𝟙 ((Modules.pushforward i).obj (SheafOfModules.unit (structureSheaf Z))) ⊗ₘ a) ≫
        moduleComparison i G =
      moduleComparison i F ≫ (Modules.pushforward i).map ((Modules.pullback i).map a) := sorry

private def cochainSource (i : Z ⟶ Y) (C : CochainComplex Y.Modules ℤ) :
    CochainComplex Y.Modules ℤ :=
  (Modules.CellTensor.replacement Y).obj
      (((Modules.pushforward i).mapHomologicalComplex (up ℤ)).obj (structureComplex Z)) ⊗
    (Modules.CellTensor.replacement Y).obj C

private def cochainTarget (i : Z ⟶ Y) (C : CochainComplex Y.Modules ℤ) :
    CochainComplex Y.Modules ℤ :=
  ((Modules.pushforward i).mapHomologicalComplex (up ℤ)).obj
    (((Modules.pullback i).mapHomologicalComplex (up ℤ)).obj
      ((Modules.CellTensor.replacement Y).obj C))

private def singleTensorColumnComparison (i : Z ⟶ Y) (P : CochainComplex Y.Modules ℤ) :
    ((((curriedTensor Y.Modules).mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj
      ((HomologicalComplex.single Y.Modules (up ℤ) 0).obj
        ((Modules.pushforward i).obj (SheafOfModules.unit (structureSheaf Z))))).obj P).X 0 ⟶
      ((Modules.pushforward i).mapHomologicalComplex (up ℤ)).obj
        (((Modules.pullback i).mapHomologicalComplex (up ℤ)).obj P) where
  f n := moduleComparison i (P.X n)
  comm' a b _ := by
    change moduleComparison i (P.X a) ≫
        (Modules.pushforward i).map ((Modules.pullback i).map (P.d a b)) =
      ((Modules.pushforward i).obj (SheafOfModules.unit (structureSheaf Z)) ◁
        P.d a b) ≫ moduleComparison i (P.X b)
    simpa only [MonoidalCategory.id_tensorHom] using
      (moduleComparison_naturality i (P.d a b)).symm

private def singleTensorComparison (i : Z ⟶ Y) (P : CochainComplex Y.Modules ℤ) :
    (HomologicalComplex.single Y.Modules (up ℤ) 0).obj
        ((Modules.pushforward i).obj (SheafOfModules.unit (structureSheaf Z))) ⊗ P ⟶
      ((Modules.pushforward i).mapHomologicalComplex (up ℤ)).obj
        (((Modules.pullback i).mapHomologicalComplex (up ℤ)).obj P) :=
  HomologicalComplex₂.ZeroColumn.Single.fromTotal
    (HomologicalComplex.mkHomToSingle (singleTensorColumnComparison i P) (by
      intro a ha
      apply HomologicalComplex.Hom.ext
      funext n
      change ((curriedTensor Y.Modules).map
          (((HomologicalComplex.single Y.Modules (up ℤ) 0).obj
            ((Modules.pushforward i).obj (SheafOfModules.unit (structureSheaf Z)))).d a 0)).app
          (P.X n) ≫ _ = 0
      simp only [HomologicalComplex.single_obj_d, CategoryTheory.Functor.map_zero,
        zero_app, zero_comp]))

private def cochainComparison (i : Z ⟶ Y) (C : CochainComplex Y.Modules ℤ) :
    cochainSource i C ⟶ cochainTarget i C :=
  ((Modules.CellTensor.augmentation Y).app
      (((Modules.pushforward i).mapHomologicalComplex (up ℤ)).obj (structureComplex Z)) ⊗ₘ
        𝟙 ((Modules.CellTensor.replacement Y).obj C)) ≫
    (((HomologicalComplex.singleMapHomologicalComplex (Modules.pushforward i) (up ℤ) 0).hom.app
      (SheafOfModules.unit (structureSheaf Z))) ⊗ₘ
        𝟙 ((Modules.CellTensor.replacement Y).obj C)) ≫
    singleTensorComparison i ((Modules.CellTensor.replacement Y).obj C)

private theorem cochainComparison_quasiIso (i : Z ⟶ Y) (hi : IsClosedImmersion i)
    (C : CochainComplex Y.Modules ℤ) : QuasiIso (cochainComparison i C) := sorry

private theorem pushforwardAugmentation_quasiIso (i : Z ⟶ Y) (hi : IsClosedImmersion i)
    (C : CochainComplex Z.Modules ℤ) :
    QuasiIso (((Modules.pushforward i).mapHomologicalComplex (up ℤ)).map
      ((CochainComplex.KInjectiveResolution.Construction.augmentation.{u} Z.Modules).app C)) :=
  sorry

/-- Exact pushforward along a closed immersion is computed by degreewise pushforward,
using localization of its specified K-injective augmentation. -/
def pushforwardCochainIso (i : Z ⟶ Y) (hi : IsClosedImmersion i)
    (C : CochainComplex Z.Modules ℤ) :
    DerivedCategory.Q.obj (((Modules.pushforward i).mapHomologicalComplex (up ℤ)).obj C) ≅
      (Modules.moduleDerivedPushforward i).obj (DerivedCategory.Q.obj C) :=
  Localization.isoOfHom (DerivedCategory.Q (C := Y.Modules))
      (HomologicalComplex.quasiIso Y.Modules (up ℤ))
      (((Modules.pushforward i).mapHomologicalComplex (up ℤ)).map
        ((CochainComplex.KInjectiveResolution.Construction.augmentation.{u} Z.Modules).app C))
      (pushforwardAugmentation_quasiIso i hi C) ≪≫
    ((Functor.KInjectiveModel.fac.{u} (Modules.pushforward i)).app C).symm ≪≫
    (Functor.KInjectiveModel.isoOfModel.{u} (Modules.pushforward i)
      (Modules.moduleDerivedPushforward i) (Modules.moduleDerivedPushforward.unit i)).app
        (DerivedCategory.Q.obj C)

/-- The forward map of the exact closed-immersion computation is the canonical
cochain comparison to derived pushforward. -/
theorem pushforwardCochainIso_hom (i : Z ⟶ Y) (hi : IsClosedImmersion i)
    (C : CochainComplex Z.Modules ℤ) :
    (pushforwardCochainIso i hi C).hom = (Modules.moduleDerivedPushforward.unit i).app C :=
  sorry

private def sourceComputation (i : Z ⟶ Y) (hi : IsClosedImmersion i)
    (K : ModuleDerived Y) :
    (DerivedTensor.Right.functor K).obj
        ((Modules.moduleDerivedPushforward i).obj (DerivedCategory.Q.obj (structureComplex Z))) ≅
      DerivedCategory.Q.obj (cochainSource i (DerivedCategory.Q.objPreimage K)) :=
  DerivedTensor.Bifunctor.Right.isoApp K _ ≪≫
    (DerivedTensor.Bifunctor.functor (C := Y.Modules)).mapIso
      ((pushforwardCochainIso i hi (structureComplex Z)).symm.prod
        (DerivedCategory.Q.objObjPreimageIso K).symm) ≪≫
    Modules.CellTensor.computationIso Y
      (((Modules.pushforward i).mapHomologicalComplex (up ℤ)).obj (structureComplex Z))
      (DerivedCategory.Q.objPreimage K)

private def targetComputation (i : Z ⟶ Y) (hi : IsClosedImmersion i)
    (K : ModuleDerived Y) :
    DerivedCategory.Q.obj (cochainTarget i (DerivedCategory.Q.objPreimage K)) ≅
      (Modules.moduleDerivedPushforward i).obj
        ((Functor.LeftDerived.Homotopy.functor (Modules.pullback i)).obj K) :=
  pushforwardCochainIso i hi
      (((Modules.pullback i).mapHomologicalComplex (up ℤ)).obj
        ((Modules.CellTensor.replacement Y).obj (DerivedCategory.Q.objPreimage K))) ≪≫
    (Modules.moduleDerivedPushforward i).mapIso
      (((Modules.CellModels.pullbackUsingCells_fac i).app (DerivedCategory.Q.objPreimage K)).symm ≪≫
        (ModuleDerived.pullback i).mapIso (DerivedCategory.Q.objObjPreimageIso K) ≪≫
        (ModuleDerived.pullbackIsoTotalLeftDerived i).app K)

/-- Tensoring the derived direct image of the structure module of a closed immersion
with a derived module computes direct image of its derived pullback. -/
def structureProjectionFormulaIso (i : Z ⟶ Y) (hi : IsClosedImmersion i)
    (K : ModuleDerived Y) :
    (DerivedTensor.Right.functor K).obj
        ((Modules.moduleDerivedPushforward i).obj (DerivedCategory.Q.obj (structureComplex Z))) ≅
      (Modules.moduleDerivedPushforward i).obj
        ((Functor.LeftDerived.Homotopy.functor (Modules.pullback i)).obj K) :=
  sourceComputation i hi K ≪≫
    Localization.isoOfHom (DerivedCategory.Q (C := Y.Modules))
      (HomologicalComplex.quasiIso Y.Modules (up ℤ))
      (cochainComparison i (DerivedCategory.Q.objPreimage K))
      (cochainComparison_quasiIso i hi (DerivedCategory.Q.objPreimage K)) ≪≫
    targetComputation i hi K

private def tensorRightStructureHom (T : AlgebraicSpace S) (N : ModuleDerived T) :
    (DerivedTensor.Right.functor (DerivedCategory.Q.obj (structureComplex T))).obj N ⟶ N :=
  (DerivedTensor.Bifunctor.Right.isoApp (DerivedCategory.Q.obj (structureComplex T)) N).hom ≫
    (DerivedTensor.Bifunctor.functor (C := T.Modules)).map
      (Prod.mkHom (DerivedCategory.Q.objObjPreimageIso N).inv
        (DerivedCategory.Q.map
          ((HomologicalComplex.single T.Modules (up ℤ) 0).map
            (Modules.structureModuleIsoTensorUnit T).hom))) ≫
    DerivedTensor.Bifunctor.counitAppOfQ (DerivedCategory.Q.objPreimage N)
      (𝟙_ (CochainComplex T.Modules ℤ)) ≫
    DerivedCategory.Q.map (ρ_ (DerivedCategory.Q.objPreimage N)).hom ≫
    (DerivedCategory.Q.objObjPreimageIso N).hom

/-- The structure-module projection comparison has forward map given by the
canonical projection mate followed by the structure-unit comparison. -/
theorem structureProjectionFormulaIso_hom (i : Z ⟶ Y) (hi : IsClosedImmersion i)
    (K : ModuleDerived Y) :
    (structureProjectionFormulaIso i hi K).hom =
      DerivedQCoh.leftMate i (DerivedCategory.Q.obj (structureComplex Z)) K ≫
        (Modules.moduleDerivedPushforward i).map
          ((DerivedTensor.Bifunctor.Right.comm (DerivedCategory.Q.obj (structureComplex Z))
            ((Functor.LeftDerived.Homotopy.functor (Modules.pullback i)).obj K)).hom ≫
              tensorRightStructureHom Z
                ((Functor.LeftDerived.Homotopy.functor (Modules.pullback i)).obj K)) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.ClosedImmersion

