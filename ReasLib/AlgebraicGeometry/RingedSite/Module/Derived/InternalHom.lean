/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Over
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.RingedSiteDerived

attribute [instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

noncomputable section

universe u

namespace RingedSite.Hom.ModuleDerived.InternalHom

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/-- A K-injective cochain representative selected by the integral K-injective localization. -/
def injectiveModel (K : max J O) : CochainComplex (ringedSiteModuleCategory J O) ℤ :=
  let localization : _ ⥤ max J O :=
    CochainComplex.Enriched.Over.KInjective.localization
      (R := ℤ) (C := ringedSiteModuleCategory J O)
  (@Functor.objPreimage _ _ _ _ localization
    (Localization.essSurj localization
      (CochainComplex.Enriched.Over.KInjective.qis
        (R := ℤ) (C := ringedSiteModuleCategory J O))) K).obj.obj

/-- The selected K-injective representative has derived image isomorphic to the given object. -/
def injectiveModelIso (K : max J O) :
    (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O).obj
      (injectiveModel K) ≅ K :=
  let localization : _ ⥤ max J O :=
    CochainComplex.Enriched.Over.KInjective.localization
      (R := ℤ) (C := ringedSiteModuleCategory J O)
  (CochainComplex.Enriched.Over.derivedQObjIso
    (R := ℤ) (A := ringedSiteModuleCategory J O) (injectiveModel K)).symm ≪≫
    @Functor.objObjPreimageIso _ _ _ _ localization
      (Localization.essSurj localization
        (CochainComplex.Enriched.Over.KInjective.qis
          (R := ℤ) (C := ringedSiteModuleCategory J O))) K

/-- The representative selected by K-injective localization is K-injective. -/
instance injectiveModel_isKInjective (K : max J O) : (injectiveModel K).IsKInjective := sorry

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
