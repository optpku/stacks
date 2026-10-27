/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.InternalHom.Bifunctor
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Symmetric
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Bidual

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.RingedSite SheafOfModules.RingedSite.RingedSiteDerived

noncomputable section

set_option backward.privateInPublic true

universe u v

namespace RingedSite.Hom.ModuleDerived.InternalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}

private def strictBidualApp
    (I F : CochainComplex (ringedSiteModuleCategory J O) ℤ) :
    F ⟶ (strictInternalHom.obj
      (op ((strictInternalHom.obj (op F)).obj I))).obj I := by
  let tensorExists : ∀ X Y : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasTensor X Y :=
    fun _ _ _ ↦ HasColimitsOfShape.has_colimit _
  let goodLeft : ∀ X Y Z : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
    fun _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  let goodRight : ∀ X Y Z : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
    fun _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  let tensorExt : ∀ X Y Z W : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasTensor₄ObjExt X Y Z W :=
    fun _ _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  let preservesLeft : ∀ X, PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J O))
      ((curriedTensor (ringedSiteModuleCategory J O)).obj X) :=
    fun _ ↦ PreservesColimitsOfShape.preservesColimit
  let preservesRight : ∀ X, PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J O))
      ((curriedTensor (ringedSiteModuleCategory J O)).flip.obj X) :=
    fun _ ↦ PreservesColimitsOfShape.preservesColimit
  let closed := @CochainComplex.InternalHom.monoidalClosed
    (ringedSiteModuleCategory J O)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance tensorExists goodLeft goodRight tensorExt
    preservesLeft preservesRight
  let monoidal := @HomologicalComplex.monoidalCategory
    (ringedSiteModuleCategory J O) inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance ℤ inferInstance (.up ℤ) inferInstance
    tensorExists preservesLeft preservesRight tensorExt goodLeft goodRight inferInstance
  let braided := @_root_.CochainComplex.Koszul.braidedCategory
    (ringedSiteModuleCategory J O) inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance tensorExists goodLeft goodRight tensorExt
  let H := @RightInternalHom.ofBraidedClosedOf _ inferInstance monoidal braided closed
  exact @RightInternalHom.toBidualApp _ inferInstance monoidal braided H I F

private def strictPrecompositionIso
    {F G : CochainComplex (ringedSiteModuleCategory J O) ℤ}
    (I : CochainComplex (ringedSiteModuleCategory J O) ℤ) [I.IsKInjective]
    (f : F ⟶ G) (hf : QuasiIso f) :
    objOfModels G I ≅ objOfModels F I := by
  apply Localization.isoOfHom DerivedCategory.Q
    (HomologicalComplex.quasiIso (ringedSiteModuleCategory J O) (.up ℤ))
    ((strictInternalHom.map f.op).app I)
  exact strictInternalHom_quasiIso_precomp f hf I

private def homModelToInjective (L N : max J O) :
    (strictInternalHom.obj (op ((DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O).objPreimage L))).obj (injectiveModel N) ⟶
      injectiveModel (obj L N) :=
  liftToInjectiveModel _ (obj L N) (𝟙 _)

private theorem homModelToInjective_quasiIso (L N : max J O) :
    QuasiIso (homModelToInjective (J := J) (O := O) L N) := by
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ringedSiteModuleCategory J O) _).1
  have h : DerivedCategory.Q.map (homModelToInjective (J := J) (O := O) L N) =
      (injectiveModelIso (obj L N)).inv := by
    apply (cancel_mono (injectiveModelIso (obj L N)).hom).1
    erw [Iso.inv_hom_id]
    exact liftToInjectiveModel_fac _ (obj L N) (𝟙 _)
  rw [h]
  infer_instance

/-- Canonical derived evaluation into the double sheaf-Hom dual, obtained by localizing
strict cochain evaluation and its specified K-injective comparison. -/
def toBidualApp (N L : max J O) :
    L ⟶ (sourceFunctor N).obj (op ((sourceFunctor N).obj (op L))) :=
  (DerivedCategory.Q.objObjPreimageIso L).inv ≫
    DerivedCategory.Q.map (strictBidualApp (J := J) (O := O) (injectiveModel N)
      ((DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O).objPreimage L)) ≫
    (strictPrecompositionIso (J := J) (O := O) (injectiveModel N) (homModelToInjective (J := J) (O := O) L N)
      (homModelToInjective_quasiIso (J := J) (O := O) L N)).inv ≫
    (modelComparisonIso (obj L N) N).hom

/-- Derived evaluation is natural in the complex being dualized. -/
theorem toBidualApp_naturality (N : max J O) {L M : max J O} (f : L ⟶ M) :
    f ≫ toBidualApp N M = toBidualApp N L ≫
      ((sourceFunctor N).rightOp ⋙ sourceFunctor N).map f := sorry

/-- Canonical evaluation from the identity to double derived sheaf-Hom dualization. -/
def toBidual (N : max J O) : 𝟭 (max J O) ⟶
    (sourceFunctor N).rightOp ⋙ sourceFunctor N where
  app L := toBidualApp N L
  naturality _ _ f := toBidualApp_naturality N f

/-- Any cochain representative and K-injective target identify derived bidual evaluation
with the localization of strict cochain evaluation. -/
theorem toBidualApp_model (L N : max J O)
    (F I : CochainComplex (ringedSiteModuleCategory J O) ℤ) [I.IsKInjective]
    (sourceIso : DerivedCategory.Q.obj F ≅ L)
    (targetIso : DerivedCategory.Q.obj I ≅ N) :
    ∃ e : obj (obj L N) N ≅
      objOfModels ((strictInternalHom.obj (op F)).obj I) I,
      toBidualApp N L ≫ e.hom =
        sourceIso.inv ≫ DerivedCategory.Q.map (strictBidualApp (J := J) (O := O) I F) := sorry

end RingedSite.Hom.ModuleDerived.InternalHom
