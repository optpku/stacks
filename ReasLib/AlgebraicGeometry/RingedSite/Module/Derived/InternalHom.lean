/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Over
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Construction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.RingedSiteDerived

attribute [instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

noncomputable section

universe u v

namespace RingedSite.Hom.ModuleDerived.InternalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- The explicit K-injective replacement of an ordinary derived representative. -/
def injectiveModel (K : max J O) : CochainComplex (ringedSiteModuleCategory J O) ℤ :=
  (CochainComplex.KInjectiveResolution.Construction.replacement
    (ringedSiteModuleCategory J O)).obj
      ((DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O).objPreimage K)

/-- The selected K-injective representative has derived image isomorphic to the given object. -/
def injectiveModelIso (K : max J O) :
    (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O).obj
      (injectiveModel K) ≅ K :=
  (Localization.isoOfHom DerivedCategory.Q
    (HomologicalComplex.quasiIso (ringedSiteModuleCategory J O) (.up ℤ))
    ((CochainComplex.KInjectiveResolution.Construction.augmentation
      (ringedSiteModuleCategory J O)).app (DerivedCategory.Q.objPreimage K))
    (CochainComplex.KInjectiveResolution.Construction.augmentation_quasiIso
      (ringedSiteModuleCategory J O) _)).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso K

/-- The explicit replacement representative is K-injective. -/
instance injectiveModel_isKInjective (K : max J O) : (injectiveModel K).IsKInjective :=
  CochainComplex.KInjectiveResolution.Construction.replacement_isKInjective
    (ringedSiteModuleCategory J O) _

/-- The derived image of the product-valued sheaf internal-Hom complex of two models. -/
def objOfModels (F I : CochainComplex (ringedSiteModuleCategory J O) ℤ) : max J O :=
  let tensorExists : ∀ X Y : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasTensor X Y :=
    fun _ _ _ ↦ Limits.HasColimitsOfShape.has_colimit _
  let goodLeft : ∀ X Y Z : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
    fun _ _ _ _ _ ↦ Limits.PreservesColimitsOfShape.preservesColimit
  let goodRight : ∀ X Y Z : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
    fun _ _ _ _ _ ↦ Limits.PreservesColimitsOfShape.preservesColimit
  let tensorExt : ∀ X Y Z W : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasTensor₄ObjExt X Y Z W :=
    fun _ _ _ _ _ _ ↦ Limits.PreservesColimitsOfShape.preservesColimit
  (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O).obj
    (@CochainComplex.InternalHom.obj (ringedSiteModuleCategory J O)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance tensorExists goodLeft goodRight tensorExt
      (fun _ ↦ Limits.PreservesColimitsOfShape.preservesColimit)
      (fun _ ↦ Limits.PreservesColimitsOfShape.preservesColimit) F I)

/-- Sheaf-valued derived internal Hom, computed with a K-injective target representative. -/
def obj (L N : max J O) : max J O :=
  objOfModels
    ((DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O).objPreimage L)
    (injectiveModel N)

/-- Any source model and any K-injective target model compute sheaf-valued derived internal Hom. -/
theorem obj_model (L N : max J O)
    (F I : CochainComplex (ringedSiteModuleCategory J O) ℤ) [I.IsKInjective]
    (sourceIso :
      (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O).obj F ≅ L)
    (targetIso :
      (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O).obj I ≅ N) :
    IsIsomorphic (obj L N) (objOfModels F I) := sorry

end RingedSite.Hom.ModuleDerived.InternalHom
