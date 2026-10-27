/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.InverseImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent.FppfSheaf
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Single
public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseLift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Small-étale module comparisons are invertible over flat locally finitely presented maps. -/
def HasFlatLfpModuleComparison {X : GroupoidsOver S} (F : etaleModules X) : Prop :=
  ∀ {x y : X.total} (φ : x ⟶ y),
    Flat (X.p.map φ).left → LocallyOfFinitePresentation (X.p.map φ).left →
      IsIso (moduleComparison φ F)

/-- The flat locally finitely presented comparison condition is pointwise invertibility. -/
theorem hasFlatLfpModuleComparison_iff {X : GroupoidsOver S} (F : etaleModules X) :
    HasFlatLfpModuleComparison F ↔
      ∀ {x y : X.total} (φ : x ⟶ y),
        Flat (X.p.map φ).left → LocallyOfFinitePresentation (X.p.map φ).left →
          IsIso (moduleComparison φ F) := sorry

/-- An étale module whose underlying module presheaf is an fppf sheaf defines an fppf module. -/
def toFppfModule {X : GroupoidsOver S} (F : etaleModules X)
    (hF : Presheaf.IsSheaf X.fppfTopology F.val.presheaf) :
    RingedSite.ModuleCat.{u} (ringedSite X) where
  val := etaleModulePresheaf F
  isSheaf :=
    (Presheaf.isSheaf_of_iso_iff (J := X.fppfTopology)
      ((PresheafOfModules.restrictScalarsCompToPresheaf
        (fppfToEtaleStructurePresheaf X)).app F.val)).mpr hF

/-- Packaging an étale module in the fppf topology preserves its module presheaf. -/
theorem toFppfModule_val {X : GroupoidsOver S} (F : etaleModules X)
    (hF : Presheaf.IsSheaf X.fppfTopology F.val.presheaf) :
    (toFppfModule F hF).val = etaleModulePresheaf F := sorry

namespace FppfEtale

/-- The underlying abelian sheaf of an étale module with its carrier universe lifted. -/
def etaleAbelianSheaf {X : GroupoidsOver S} (F : etaleModules X) :
    Sheaf X.etaleTopology AddCommGrpCat.{u + 1} :=
  (SheafOfModules.toSheaf (etaleRingedSite X).structureSheaf).obj
    (RingedSite.Module.carrierLift (etaleRingedSite X) F)

/-- The underlying abelian sheaf of an fppf-packaged module with its carrier universe lifted. -/
def fppfAbelianSheaf {X : GroupoidsOver S} (F : etaleModules X)
    (hF : Presheaf.IsSheaf X.fppfTopology F.val.presheaf) :
    Sheaf X.fppfTopology AddCommGrpCat.{u + 1} :=
  (SheafOfModules.toSheaf (ringedSite X).structureSheaf).obj
    (RingedSite.Module.carrierLift (ringedSite X) (toFppfModule F hF))

/-- Restriction of fppf modules to the étale topology is a right adjoint. -/
instance epsilonPushforward_isRightAdjoint (X : GroupoidsOver S) :
    (etaleFppfHom X).modulePushforward.{u + 1}.IsRightAdjoint := sorry

/-- The total right derived restriction of fppf modules to the étale topology. -/
def epsilonPushforwardDerived (X : GroupoidsOver S) :
    RingedSite.Hom.ModuleDerived.{u + 1} (ringedSite X) ⥤
      RingedSite.Hom.ModuleDerived.{u + 1} (etaleRingedSite X) :=
  @Functor.totalRightDerived
    (RingedSite.Hom.ModuleHomotopy.{u + 1} (ringedSite X))
    (RingedSite.Hom.ModuleDerived.{u + 1} (ringedSite X))
    (RingedSite.Hom.ModuleDerived.{u + 1} (etaleRingedSite X))
    inferInstance inferInstance inferInstance
    (RingedSite.Hom.modulePushforwardToDerived.{u + 1} (etaleFppfHom X))
    (RingedSite.Hom.moduleLocalization.{u + 1} (ringedSite X))
    (RingedSite.Hom.ModuleQis.{u + 1} (ringedSite X)) inferInstance
    (RingedSite.Hom.modulePushforwardToDerived.hasRightDerived.{u + 1} (etaleFppfHom X))

/-- Pullback from the étale topology to the fppf topology is exact. -/
theorem epsilonPullback_exact (X : GroupoidsOver S) :
    exactFunctor (RingedSite.ModuleCat.{u + 1} (etaleRingedSite X))
      (RingedSite.ModuleCat.{u + 1} (ringedSite X))
      (RingedSite.Hom.modulePullback.{u + 1} (etaleFppfHom X)) := sorry

/-- The exact module pullback from the étale topology to the fppf topology. -/
def epsilonPullbackExact (X : GroupoidsOver S) :
    RingedSite.ModuleCat.{u + 1} (etaleRingedSite X) ⥤ₑ
      RingedSite.ModuleCat.{u + 1} (ringedSite X) :=
  ⟨RingedSite.Hom.modulePullback.{u + 1} (etaleFppfHom X), epsilonPullback_exact X⟩

/-- Derived pullback from the étale topology to the fppf topology. -/
def epsilonPullbackDerived (X : GroupoidsOver S) :
    RingedSite.Hom.ModuleDerived.{u + 1} (etaleRingedSite X) ⥤
      RingedSite.Hom.ModuleDerived.{u + 1} (ringedSite X) :=
  @ExactFunctor.mapDerivedCategory
    (RingedSite.ModuleCat.{u + 1} (etaleRingedSite X)) inferInstance inferInstance
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1} (etaleRingedSite X))
    (RingedSite.ModuleCat.{u + 1} (ringedSite X)) inferInstance inferInstance
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1} (ringedSite X))
    (epsilonPullbackExact X)

/-- Étale inverse image along a morphism of categories fibred in groupoids is exact. -/
theorem etaleInverseImage_exact {X Y : GroupoidsOver S} (g : X ⟶ Y) :
    exactFunctor (RingedSite.ModuleCat.{u + 1} (etaleRingedSite Y))
      (RingedSite.ModuleCat.{u + 1} (etaleRingedSite X))
      (etaleSiteHom g).modulePushforward.{u + 1} := sorry

/-- The exact étale module inverse image along a morphism of categories fibred in groupoids. -/
def etaleInverseImageExact {X Y : GroupoidsOver S} (g : X ⟶ Y) :
    RingedSite.ModuleCat.{u + 1} (etaleRingedSite Y) ⥤ₑ
      RingedSite.ModuleCat.{u + 1} (etaleRingedSite X) :=
  ⟨(etaleSiteHom g).modulePushforward.{u + 1}, etaleInverseImage_exact g⟩

/-- Derived étale inverse image along a morphism of categories fibred in groupoids. -/
def etaleInverseImageDerived {X Y : GroupoidsOver S} (g : X ⟶ Y) :
    RingedSite.Hom.ModuleDerived.{u + 1} (etaleRingedSite Y) ⥤
      RingedSite.Hom.ModuleDerived.{u + 1} (etaleRingedSite X) :=
  @ExactFunctor.mapDerivedCategory
    (RingedSite.ModuleCat.{u + 1} (etaleRingedSite Y)) inferInstance inferInstance
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1} (etaleRingedSite Y))
    (RingedSite.ModuleCat.{u + 1} (etaleRingedSite X)) inferInstance inferInstance
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1} (etaleRingedSite X))
    (etaleInverseImageExact g)

/-- Derived fppf inverse image induced by the exact associated module inverse image. -/
def fppfInverseImageDerived {X Y : GroupoidsOver S} (g : X ⟶ Y) :
    RingedSite.Hom.ModuleDerived.{u + 1} (ringedSite Y) ⥤
      RingedSite.Hom.ModuleDerived.{u + 1} (ringedSite X) :=
  @Functor.mapDerivedCategory
    (RingedSite.ModuleCat.{u + 1} (ringedSite Y)) inferInstance inferInstance
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1} (ringedSite Y))
    (RingedSite.ModuleCat.{u + 1} (ringedSite X)) inferInstance inferInstance
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1} (ringedSite X))
    (associatedModuleInverseImage g .fppf)
    (Functor.additive_of_leftExact_or_rightExact _
      (Or.inl (associatedModuleInverseImage_preservesFiniteLimits g .fppf)))
    (associatedModuleInverseImage_preservesFiniteLimits g .fppf)
    (associatedModuleInverseImage_preservesFiniteColimits g .fppf)

end FppfEtale

end AlgebraicGeometry.GroupoidsOver
