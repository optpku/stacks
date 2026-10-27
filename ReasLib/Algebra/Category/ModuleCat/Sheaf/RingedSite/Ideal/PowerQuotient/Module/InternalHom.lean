/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.PowerQuotient.Module
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact

/-!
# Internal Hom and ideal-power quotients

Reducing evaluation modulo an ideal power gives a canonical comparison from the quotient of an
internal-Hom sheaf to the internal Hom between the corresponding module quotients.
-/

section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.InternalHom

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

private theorem action_tensorRight
    (I : Subobject (unitModule J O))
    (M N : ringedSiteModuleCategory.{u, u, u, u} J O) :
    (α_ (I : ringedSiteModuleCategory J O) M N).hom ≫
        action I (tensorObj M N) =
      action I M ▷ N := by
  simp [action]

private noncomputable def powerActionZeroIso
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, u, u, u} J O) :
    tensorObj (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) 0) M ≅ M :=
  (unitIsoTensorUnit (J := J) (𝒪 := O) ▷ᵢ M) ≪≫ λ_ M

@[reducible] private noncomputable def iteratedSource
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, u, u, u} J O) : ℕ →
      ringedSiteModuleCategory.{u, u, u, u} J O
  | 0 => M
  | n + 1 => tensorObj (I : ringedSiteModuleCategory J O) (iteratedSource I M n)

private noncomputable def iteratedAction
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, u, u, u} J O) :
    (n : ℕ) → iteratedSource I M n ⟶ M
  | 0 => 𝟙 M
  | n + 1 => action I (iteratedSource I M n) ≫ iteratedAction I M n

private noncomputable def coreSourceIso
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, u, u, u} J O) :
    (n : ℕ) →
      tensorObj (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) M ≅
        iteratedSource I M n
  | 0 => powerActionZeroIso I M
  | n + 1 =>
      (α_ (I : ringedSiteModuleCategory J O)
        (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) M) ≪≫
      (Iso.refl (I : ringedSiteModuleCategory J O) ⊗ᵢ coreSourceIso I M n)

private theorem coreSourceIso_hom_comp_iteratedAction
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, u, u, u} J O) :
    ∀ n : ℕ,
      (coreSourceIso I M n).hom ≫ iteratedAction I M n = powerAction I M n
  | 0 => by
      change (powerActionZeroIso I M).hom ≫ 𝟙 M = (powerActionZeroIso I M).hom
      exact Category.comp_id _
  | n + 1 => by
      have hIso := action_naturality I (coreSourceIso I M n).hom
      change ((I : ringedSiteModuleCategory J O) ◁ (coreSourceIso I M n).hom) ≫
          action I (iteratedSource I M n) =
        action I (tensorObj
          (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) M) ≫
          (coreSourceIso I M n).hom at hIso
      have hPower := action_naturality I (powerAction I M n)
      change ((I : ringedSiteModuleCategory J O) ◁ powerAction I M n) ≫ action I M =
        action I (tensorObj
          (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) M) ≫
          powerAction I M n at hPower
      rw [powerAction_succ]
      dsimp only [coreSourceIso, iteratedAction]
      simp only [Iso.trans_hom, MonoidalCategory.tensorIso_hom,
        MonoidalCategory.tensorHom_def, Iso.refl_hom, id_whiskerRight, Category.id_comp]
      change (α_ (I : ringedSiteModuleCategory J O)
          (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) M).hom ≫
        (((I : ringedSiteModuleCategory J O) ◁ (coreSourceIso I M n).hom) ≫
          action I (iteratedSource I M n) ≫ iteratedAction I M n) = _
      exact congrArg
        (fun k ↦ (α_ (I : ringedSiteModuleCategory J O)
          (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) M).hom ≫ k)
        (calc
          ((I : ringedSiteModuleCategory J O) ◁ (coreSourceIso I M n).hom) ≫
                action I (iteratedSource I M n) ≫ iteratedAction I M n =
              (((I : ringedSiteModuleCategory J O) ◁ (coreSourceIso I M n).hom) ≫
                action I (iteratedSource I M n)) ≫ iteratedAction I M n :=
            (Category.assoc _ _ _).symm
          _ = (action I (tensorObj
                (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) M) ≫
                (coreSourceIso I M n).hom) ≫ iteratedAction I M n :=
            congrArg (fun k ↦ k ≫ iteratedAction I M n) hIso
          _ = action I (tensorObj
                (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) M) ≫
              ((coreSourceIso I M n).hom ≫ iteratedAction I M n) :=
            Category.assoc _ _ _
          _ = action I (tensorObj
                (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) M) ≫
              powerAction I M n := congrArg _
            (coreSourceIso_hom_comp_iteratedAction I M n)
          _ = ((I : ringedSiteModuleCategory J O) ◁ powerAction I M n) ≫
              action I M := hPower.symm)

private noncomputable def iteratedActionTensorRightFactor
    (I : Subobject (unitModule J O))
    {M N P : ringedSiteModuleCategory.{u, u, u, u} J O} (b : tensorObj M N ⟶ P) :
    (n : ℕ) → tensorObj (iteratedSource I M n) N ⟶ iteratedSource I P n
  | 0 => b
  | n + 1 =>
      (α_ (I : ringedSiteModuleCategory J O) (iteratedSource I M n) N).hom ≫
        ((I : ringedSiteModuleCategory J O) ◁ iteratedActionTensorRightFactor I b n)

private theorem iteratedAction_whiskerRight
    (I : Subobject (unitModule J O))
    {M N P : ringedSiteModuleCategory.{u, u, u, u} J O} (b : tensorObj M N ⟶ P) :
    ∀ n : ℕ,
      (iteratedAction I M n ▷ N) ≫ b =
        iteratedActionTensorRightFactor I b n ≫ iteratedAction I P n
  | 0 => by
      simp [iteratedSource, iteratedAction, iteratedActionTensorRightFactor]
  | n + 1 => by
      calc
        (iteratedAction I M (n + 1) ▷ N) ≫ b =
            (action I (iteratedSource I M n) ▷ N) ≫
              ((iteratedAction I M n ▷ N) ≫ b) := by
            simp only [iteratedAction, comp_whiskerRight, Category.assoc]
        _ = (action I (iteratedSource I M n) ▷ N) ≫
              (iteratedActionTensorRightFactor I b n ≫ iteratedAction I P n) :=
            congrArg (fun k ↦ (action I (iteratedSource I M n) ▷ N) ≫ k)
              (iteratedAction_whiskerRight I b n)
        _ = ((α_ (I : ringedSiteModuleCategory J O) (iteratedSource I M n) N).hom ≫
              action I (tensorObj (iteratedSource I M n) N)) ≫
                (iteratedActionTensorRightFactor I b n ≫ iteratedAction I P n) := by
            exact congrArg
              (fun k ↦ k ≫
                (iteratedActionTensorRightFactor I b n ≫ iteratedAction I P n))
              (action_tensorRight I (iteratedSource I M n) N).symm
        _ = (α_ (I : ringedSiteModuleCategory J O) (iteratedSource I M n) N).hom ≫
              (action I (tensorObj (iteratedSource I M n) N) ≫
                iteratedActionTensorRightFactor I b n) ≫ iteratedAction I P n := by
            simp only [Category.assoc]
        _ = (α_ (I : ringedSiteModuleCategory J O) (iteratedSource I M n) N).hom ≫
              (((I : ringedSiteModuleCategory J O) ◁
                  iteratedActionTensorRightFactor I b n) ≫
                action I (iteratedSource I P n)) ≫ iteratedAction I P n := by
            exact congrArg
              (fun k ↦
                (α_ (I : ringedSiteModuleCategory J O) (iteratedSource I M n) N).hom ≫
                  k ≫ iteratedAction I P n)
              (action_naturality I (iteratedActionTensorRightFactor I b n)).symm
        _ = iteratedActionTensorRightFactor I b (n + 1) ≫
              iteratedAction I P (n + 1) := by
            simp only [iteratedActionTensorRightFactor, iteratedAction, iteratedSource,
              Category.assoc]

private noncomputable def iteratedActionTensorLeftFactor
    (I : Subobject (unitModule J O))
    {M N P : ringedSiteModuleCategory.{u, u, u, u} J O} (b : tensorObj M N ⟶ P)
    (n : ℕ) : tensorObj M (iteratedSource I N n) ⟶ iteratedSource I P n :=
  (β_ M (iteratedSource I N n)).hom ≫
    iteratedActionTensorRightFactor I ((β_ N M).hom ≫ b) n

private theorem iteratedAction_whiskerLeft
    (I : Subobject (unitModule J O))
    {M N P : ringedSiteModuleCategory.{u, u, u, u} J O} (b : tensorObj M N ⟶ P)
    (n : ℕ) :
    (M ◁ iteratedAction I N n) ≫ b =
      iteratedActionTensorLeftFactor I b n ≫ iteratedAction I P n := by
  calc
    (M ◁ iteratedAction I N n) ≫ b =
        (M ◁ iteratedAction I N n) ≫ (β_ M N).hom ≫ (β_ N M).hom ≫ b := by
      simp only [Category.assoc, SymmetricCategory.symmetry_assoc, Category.id_comp]
    _ = (β_ M (iteratedSource I N n)).hom ≫
          (iteratedAction I N n ▷ M) ≫ (β_ N M).hom ≫ b := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ (β_ N M).hom ≫ b)
        (BraidedCategory.braiding_naturality_right M (iteratedAction I N n))
    _ = (β_ M (iteratedSource I N n)).hom ≫
          ((iteratedAction I N n ▷ M) ≫ ((β_ N M).hom ≫ b)) := by
      simp only [Category.assoc]
    _ = (β_ M (iteratedSource I N n)).hom ≫
          (iteratedActionTensorRightFactor I ((β_ N M).hom ≫ b) n ≫
            iteratedAction I P n) :=
      congrArg (fun k ↦ (β_ M (iteratedSource I N n)).hom ≫ k)
        (iteratedAction_whiskerRight I ((β_ N M).hom ≫ b) n)
    _ = iteratedActionTensorLeftFactor I b n ≫ iteratedAction I P n := by
      simp only [iteratedActionTensorLeftFactor, Category.assoc]

private noncomputable def evaluation
    (G F : ringedSiteModuleCategory.{u, u, u, u} J O) :
    tensorObj G (SheafOfModules.RingedSite.InternalHom.obj O G F) ⟶ F :=
  (SheafOfModules.RingedSite.InternalHom.homEquiv O G
    (SheafOfModules.RingedSite.InternalHom.obj O G F) F).symm
      (𝟙 (SheafOfModules.RingedSite.InternalHom.obj O G F))

private theorem evaluation_apply
    (G F : ringedSiteModuleCategory.{u, u, u, u} J O) (U : Cᵒᵖ)
    (x : G.val.obj U)
    (y : (SheafOfModules.RingedSite.InternalHom.obj O G F).val.obj U) :
    SheafOfModules.RingedSite.InternalHom.LocalHom.evalFun O G F U y x =
      ((evaluation G F).val.app U).hom
        (SheafOfModules.RingedSite.tensorSection O U x y) := by
  change SheafOfModules.RingedSite.InternalHom.LocalHom.evalFun O G F U
      (((𝟙 (SheafOfModules.RingedSite.InternalHom.obj O G F) :
        SheafOfModules.RingedSite.InternalHom.obj O G F ⟶
          SheafOfModules.RingedSite.InternalHom.obj O G F).val.app U).hom y) x = _
  rw [← SheafOfModules.RingedSite.InternalHom.Bilinear.toBilinear_app
    O (𝟙 (SheafOfModules.RingedSite.InternalHom.obj O G F)) U x y]
  rw [← SheafOfModules.RingedSite.SectionBilinearMap.ofHom_app
    (evaluation G F) U x y]
  have h := SheafOfModules.RingedSite.SectionBilinearMap.ofHom_hom
    (SheafOfModules.RingedSite.InternalHom.Bilinear.toBilinear O
      (𝟙 (SheafOfModules.RingedSite.InternalHom.obj O G F)))
  change SheafOfModules.RingedSite.SectionBilinearMap.ofHom (evaluation G F) =
    SheafOfModules.RingedSite.InternalHom.Bilinear.toBilinear O
      (𝟙 (SheafOfModules.RingedSite.InternalHom.obj O G F)) at h
  rw [h]

private noncomputable def leftDescData
    (I : Subobject (unitModule J O))
    (G F : ringedSiteModuleCategory.{u, u, u, u} J O) (n : ℕ) :
    { f : tensorObj (stage I G n)
          (SheafOfModules.RingedSite.InternalHom.obj O G F) ⟶ stage I F n //
      (projection I G n ▷ SheafOfModules.RingedSite.InternalHom.obj O G F) ≫ f =
        evaluation G F ≫ projection I F n } := by
  let H := SheafOfModules.RingedSite.InternalHom.obj O G F
  let reducedEvaluation : tensorObj G H ⟶ stage I F n :=
    evaluation G F ≫ projection I F n
  have reducedEvaluation_zero_left :
      (powerAction I G n ▷ H) ≫ reducedEvaluation = 0 := by
    dsimp [reducedEvaluation]
    have iteratedAction_comp_projection :
        iteratedAction I F n ≫ projection I F n = 0 := by
      apply (cancel_epi (coreSourceIso I F n).hom).1
      rw [← Category.assoc, coreSourceIso_hom_comp_iteratedAction,
        cokernel.condition]
      simp
    have iterated_zero :
        (iteratedAction I G n ▷ H) ≫ evaluation G F ≫ projection I F n = 0 := by
      rw [← Category.assoc, iteratedAction_whiskerRight I (evaluation G F) n]
      rw [Category.assoc, iteratedAction_comp_projection, comp_zero]
    rw [← coreSourceIso_hom_comp_iteratedAction I G n]
    have iterated_zero' :
        (iteratedAction I G n ▷ H) ≫ evaluation G F ≫
          cokernel.π (powerAction I F n) = 0 := by
      simpa only [projection] using iterated_zero
    simpa only [comp_whiskerRight, Category.assoc, comp_zero] using
      congrArg (fun k ↦ ((coreSourceIso I G n).hom ▷ H) ≫ k) iterated_zero'
  let hAddRight : (tensorRight H).Additive :=
    @tensorRight_additive _ _ _ _
      (SheafOfModules.RingedSite.monoidalPreadditive (O := O)) H
  let hZeroRight : (tensorRight H).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ (tensorRight H) hAddRight
  let eRight : (tensorRight H).obj (stage I G n) ≅
      cokernel ((tensorRight H).map (powerAction I G n)) :=
    @PreservesCokernel.iso _ _ _ _ _ _ (tensorRight H) hZeroRight _ _
      (powerAction I G n) _ _
      (SheafOfModules.RingedSite.tensorRightPreservesColimitsOfShape
        (O := O) H).preservesColimit
  let f := eRight.hom ≫
    cokernel.desc ((tensorRight H).map (powerAction I G n)) reducedEvaluation (by
      change (powerAction I G n ▷ H) ≫ reducedEvaluation = 0
      exact reducedEvaluation_zero_left)
  have f_spec : (projection I G n ▷ H) ≫ f = reducedEvaluation := by
    change (tensorRight H).map (projection I G n) ≫ f = reducedEvaluation
    dsimp only [f]
    rw [← Category.assoc]
    have h :
        (tensorRight H).map (projection I G n) ≫ eRight.hom =
          cokernel.π ((tensorRight H).map (powerAction I G n)) := by
      exact @PreservesCokernel.π_iso_hom _ _ _ _ _ _ (tensorRight H) hZeroRight _ _
        (powerAction I G n) _ _
        (SheafOfModules.RingedSite.tensorRightPreservesColimitsOfShape
          (O := O) H).preservesColimit
    rw [h]
    apply cokernel.π_desc
  exact ⟨f, f_spec⟩

private noncomputable abbrev leftDesc
    (I : Subobject (unitModule J O))
    (G F : ringedSiteModuleCategory.{u, u, u, u} J O) (n : ℕ) :=
  (leftDescData I G F n).1

@[reassoc] private theorem projection_whiskerRight_comp_leftDesc
    (I : Subobject (unitModule J O))
    (G F : ringedSiteModuleCategory.{u, u, u, u} J O) (n : ℕ) :
    (projection I G n ▷ SheafOfModules.RingedSite.InternalHom.obj O G F) ≫
        leftDesc I G F n =
      evaluation G F ≫ projection I F n := by
  exact (leftDescData I G F n).2

private noncomputable def descendedEvaluationData
    (I : Subobject (unitModule J O))
    (G F : ringedSiteModuleCategory.{u, u, u, u} J O) (n : ℕ) :
    { f : tensorObj (stage I G n)
          (stage I (SheafOfModules.RingedSite.InternalHom.obj O G F) n) ⟶
        stage I F n //
      ((stage I G n) ◁ projection I
          (SheafOfModules.RingedSite.InternalHom.obj O G F) n) ≫ f =
        leftDesc I G F n } := by
  let H := SheafOfModules.RingedSite.InternalHom.obj O G F
  let reducedEvaluation : tensorObj G H ⟶ stage I F n :=
    evaluation G F ≫ projection I F n
  have iteratedAction_comp_projection :
      iteratedAction I F n ≫ projection I F n = 0 := by
    apply (cancel_epi (coreSourceIso I F n).hom).1
    rw [← Category.assoc, coreSourceIso_hom_comp_iteratedAction,
      cokernel.condition]
    simp
  have iterated_zero :
      (G ◁ iteratedAction I H n) ≫ reducedEvaluation = 0 := by
    dsimp [reducedEvaluation]
    rw [← Category.assoc, iteratedAction_whiskerLeft I (evaluation G F) n]
    rw [Category.assoc, iteratedAction_comp_projection, comp_zero]
  have reducedEvaluation_zero_right :
      (G ◁ powerAction I H n) ≫ reducedEvaluation = 0 := by
    rw [← coreSourceIso_hom_comp_iteratedAction I H n]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [iterated_zero, comp_zero]

  have projection_whiskerRight_epi : Epi (projection I G n ▷
      tensorObj (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) H) := by
    change Epi ((tensorRight
      (tensorObj (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) H)).map
        (projection I G n))
    exact @Functor.map_epi _ _ _ _
      (tensorRight (tensorObj
        (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) H))
      (@preservesEpimorphisms_of_preservesColimitsOfShape _ _ _ _
        (tensorRight (tensorObj
          (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) H))
        (SheafOfModules.RingedSite.tensorRightPreservesColimitsOfShape
          (O := O) (tensorObj
            (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) H)))
      _ _ (projection I G n) inferInstance
  have right_zero :
      ((stage I G n) ◁ powerAction I H n) ≫ leftDesc I G F n = 0 := by
    exact projection_whiskerRight_epi.left_cancellation _ _ (by
      rw [← MonoidalCategory.whisker_exchange_assoc,
        projection_whiskerRight_comp_leftDesc,
        reducedEvaluation_zero_right]
      simp)

  let hAddLeft : (tensorLeft (stage I G n)).Additive :=
    @tensorLeft_additive _ _ _ _
      (SheafOfModules.RingedSite.monoidalPreadditive (O := O)) (stage I G n)
  let hZeroLeft : (tensorLeft (stage I G n)).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
      (tensorLeft (stage I G n)) hAddLeft
  let eLeft : (tensorLeft (stage I G n)).obj (stage I H n) ≅
      cokernel ((tensorLeft (stage I G n)).map (powerAction I H n)) :=
    @PreservesCokernel.iso _ _ _ _ _ _ (tensorLeft (stage I G n)) hZeroLeft _ _
      (powerAction I H n) _ _
      (SheafOfModules.RingedSite.tensorLeftPreservesColimitsOfShape
        (O := O) (stage I G n)).preservesColimit
  let leftDesc' : (tensorLeft (stage I G n)).obj H ⟶ stage I F n :=
    leftDesc I G F n
  let f := eLeft.hom ≫
    cokernel.desc ((tensorLeft (stage I G n)).map (powerAction I H n))
      leftDesc' (by
        change ((stage I G n) ◁ powerAction I H n) ≫ leftDesc' = 0
        dsimp only [leftDesc']
        exact right_zero)
  have f_spec : (tensorLeft (stage I G n)).map (projection I H n) ≫ f = leftDesc' := by
    dsimp only [f]
    rw [← Category.assoc]
    have h :
        (tensorLeft (stage I G n)).map (projection I H n) ≫ eLeft.hom =
          cokernel.π ((tensorLeft (stage I G n)).map (powerAction I H n)) := by
      exact @PreservesCokernel.π_iso_hom _ _ _ _ _ _
        (tensorLeft (stage I G n)) hZeroLeft _ _ (powerAction I H n) _ _
        (SheafOfModules.RingedSite.tensorLeftPreservesColimitsOfShape
          (O := O) (stage I G n)).preservesColimit
    rw [h]
    apply cokernel.π_desc
  refine ⟨f, ?_⟩
  change (tensorLeft (stage I G n)).map (projection I H n) ≫ f = leftDesc'
  exact f_spec

private noncomputable abbrev descendedEvaluation
    (I : Subobject (unitModule J O))
    (G F : ringedSiteModuleCategory.{u, u, u, u} J O) (n : ℕ) :=
  (descendedEvaluationData I G F n).1

@[reassoc] private theorem whiskerLeft_projection_comp_descendedEvaluation
    (I : Subobject (unitModule J O))
    (G F : ringedSiteModuleCategory.{u, u, u, u} J O) (n : ℕ) :
    ((stage I G n) ◁ projection I
        (SheafOfModules.RingedSite.InternalHom.obj O G F) n) ≫
      descendedEvaluation I G F n = leftDesc I G F n := by
  exact (descendedEvaluationData I G F n).2

private theorem descendedEvaluation_step
    (I : Subobject (unitModule J O))
    (G F : ringedSiteModuleCategory.{u, u, u, u} J O) (n : ℕ) :
    (step I G n ⊗ₘ
        step I (SheafOfModules.RingedSite.InternalHom.obj O G F) n) ≫
        descendedEvaluation I G F n =
      descendedEvaluation I G F (n + 1) ≫ step I F n := by
  let H := SheafOfModules.RingedSite.InternalHom.obj O G F
  have hRight : Epi (projection I G (n + 1) ▷ H) := by
    change Epi ((tensorRight H).map (projection I G (n + 1)))
    exact @Functor.map_epi _ _ _ _ (tensorRight H)
      (@preservesEpimorphisms_of_preservesColimitsOfShape _ _ _ _ (tensorRight H)
        (SheafOfModules.RingedSite.tensorRightPreservesColimitsOfShape
          (O := O) H)) _ _ (projection I G (n + 1)) inferInstance
  have hLeft :
      Epi ((stage I G (n + 1)) ◁ projection I H (n + 1)) := by
    change Epi ((tensorLeft (stage I G (n + 1))).map (projection I H (n + 1)))
    exact @Functor.map_epi _ _ _ _ (tensorLeft (stage I G (n + 1)))
      (@preservesEpimorphisms_of_preservesColimitsOfShape _ _ _ _
        (tensorLeft (stage I G (n + 1)))
        (SheafOfModules.RingedSite.tensorLeftPreservesColimitsOfShape
          (O := O) (stage I G (n + 1)))) _ _ (projection I H (n + 1)) inferInstance
  exact hLeft.left_cancellation _ _ (hRight.left_cancellation _ _ (by
    dsimp only [H]
    simp only [MonoidalCategory.tensorHom_def, Category.assoc]
    rw [MonoidalCategory.whisker_exchange_assoc]
    rw [← MonoidalCategory.comp_whiskerRight_assoc]
    rw [projection_comp_step]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [projection_comp_step]
    rw [whiskerLeft_projection_comp_descendedEvaluation]
    rw [projection_whiskerRight_comp_leftDesc]
    rw [whiskerLeft_projection_comp_descendedEvaluation_assoc]
    rw [projection_whiskerRight_comp_leftDesc_assoc]
    rw [projection_comp_step]))

/-- Reduction of an internal-Hom sheaf modulo `I ^ n` maps canonically to the internal Hom
between the corresponding reduced module sheaves. -/
public noncomputable def comparison
    (I : Subobject (unitModule J O))
    (G F : ringedSiteModuleCategory.{u, u, u, u} J O) (n : ℕ) :
    stage I (SheafOfModules.RingedSite.InternalHom.obj O G F) n ⟶
      SheafOfModules.RingedSite.InternalHom.obj O (stage I G n) (stage I F n) :=
  SheafOfModules.RingedSite.InternalHom.homEquiv O (stage I G n)
    (stage I (SheafOfModules.RingedSite.InternalHom.obj O G F) n) (stage I F n)
      (descendedEvaluation I G F n)

private theorem comparison_apply_descended
    (I : Subobject (unitModule J O))
    (G F : ringedSiteModuleCategory.{u, u, u, u} J O) (n : ℕ)
    (U : Cᵒᵖ)
    (x : (stage I G n).val.obj U)
    (y : (stage I (SheafOfModules.RingedSite.InternalHom.obj O G F) n).val.obj U) :
    SheafOfModules.RingedSite.InternalHom.LocalHom.evalFun O
        (stage I G n) (stage I F n) U (((comparison I G F n).val.app U).hom y) x =
      ((descendedEvaluation I G F n).val.app U).hom
        (SheafOfModules.RingedSite.tensorSection O U x y) := by
  rw [← SheafOfModules.RingedSite.InternalHom.Bilinear.toBilinear_app
    O (comparison I G F n) U x y]
  with_unfolding_all
    change (SheafOfModules.RingedSite.InternalHom.Bilinear.toBilinear O
        (SheafOfModules.RingedSite.InternalHom.Bilinear.ofBilinear O
          (SheafOfModules.RingedSite.SectionBilinearMap.ofHom
            (descendedEvaluation I G F n)))).app U x y = _
  rw [SheafOfModules.RingedSite.InternalHom.Bilinear.toBilinear_ofBilinear,
    SheafOfModules.RingedSite.SectionBilinearMap.ofHom_app]

private theorem projection_tensor_projection_comp_descendedEvaluation
    (I : Subobject (unitModule J O))
    (G F : ringedSiteModuleCategory.{u, u, u, u} J O) (n : ℕ) :
    (projection I G n ⊗ₘ projection I
        (SheafOfModules.RingedSite.InternalHom.obj O G F) n) ≫
      descendedEvaluation I G F n = evaluation G F ≫ projection I F n := by
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]
  rw [whiskerLeft_projection_comp_descendedEvaluation,
    projection_whiskerRight_comp_leftDesc]

/-- The internal-Hom comparison evaluates projected local sections by ordinary evaluation,
followed by the target quotient projection. -/
public theorem comparison_apply
    (I : Subobject (unitModule J O))
    (G F : ringedSiteModuleCategory.{u, u, u, u} J O) (n : ℕ)
    (U : Cᵒᵖ) (x : G.val.obj U)
    (y : (SheafOfModules.RingedSite.InternalHom.obj O G F).val.obj U) :
    SheafOfModules.RingedSite.InternalHom.LocalHom.evalFun O
        (stage I G n) (stage I F n) U
        (((comparison I G F n).val.app U).hom
          (((projection I (SheafOfModules.RingedSite.InternalHom.obj O G F) n).val.app U).hom y))
        (((projection I G n).val.app U).hom x) =
      ((projection I F n).val.app U).hom
        (SheafOfModules.RingedSite.InternalHom.LocalHom.evalFun O G F U y x) := by
  rw [comparison_apply_descended, evaluation_apply]
  have h := congrArg
    (fun f ↦ (f.val.app U).hom (SheafOfModules.RingedSite.tensorSection O U x y))
    (projection_tensor_projection_comp_descendedEvaluation I G F n)
  simpa [SheafOfModules.RingedSite.tensorSection_naturality] using h

set_option maxHeartbeats 400000 in
/-- Morphisms classified by the internal-Hom comparison commute with the successor quotient
transitions. -/
public theorem comparison_step
    (I : Subobject (unitModule J O))
    (G F : ringedSiteModuleCategory.{u, u, u, u} J O) (n : ℕ)
    (s : (stage I (SheafOfModules.RingedSite.InternalHom.obj O G F) (n + 1)).sections) :
    step I G n ≫
        SheafOfModules.RingedSite.InternalHom.sectionsHomEquiv O (stage I G n) (stage I F n)
          (SheafOfModules.sectionsMap (comparison I G F n)
            (SheafOfModules.sectionsMap
              (step I (SheafOfModules.RingedSite.InternalHom.obj O G F) n) s)) =
      SheafOfModules.RingedSite.InternalHom.sectionsHomEquiv O
          (stage I G (n + 1)) (stage I F (n + 1))
          (SheafOfModules.sectionsMap (comparison I G F (n + 1)) s) ≫
        step I F n := by
  ext U x
  have h := congrArg
    (fun f ↦ (f.val.app U).hom
      (SheafOfModules.RingedSite.tensorSection O U x (s.val U)))
    (descendedEvaluation_step I G F n)
  change SheafOfModules.RingedSite.InternalHom.LocalHom.evalFun O
      (stage I G n) (stage I F n) U
        (((comparison I G F n).val.app U).hom
          (((step I (SheafOfModules.RingedSite.InternalHom.obj O G F) n).val.app U).hom
            (s.val U)))
        (((step I G n).val.app U).hom x) =
    ((step I F n).val.app U).hom
      (SheafOfModules.RingedSite.InternalHom.LocalHom.evalFun O
        (stage I G (n + 1)) (stage I F (n + 1)) U
          (((comparison I G F (n + 1)).val.app U).hom (s.val U)) x)
  rw [comparison_apply_descended, comparison_apply_descended]
  simpa [SheafOfModules.RingedSite.tensorSection_naturality] using h

end SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.InternalHom

end
