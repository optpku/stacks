/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedSections.Abelian
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Underlying
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Functor CategoryTheory.Limits ComplexShape
open RingedSite.Hom
open RingedSite.Cocontinuous
open Functor.RightDerived

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
variable [UnivLE.{u + 1, z}]

/-- Restriction of additive global sections of modules along the lisse-étale inclusion. -/
def lisseEtaleModuleGlobalSectionsComparison :
    moduleGlobalSectionsAdditiveFunctor.{z} (etaleRingedSite X) ⟶
      (moduleInverseImage (J := lisseEtaleTopology X) (K := X.etaleTopology)
        (lisseEtaleInclusion X) (etaleStructureSheaf X)) ⋙
        moduleGlobalSectionsAdditiveFunctor.{z} (lisseEtaleRingedSite X) :=
  whiskerLeft (SheafOfModules.toSheaf (etaleStructureSheaf X))
    (@Sheaf.globalSectionsPushforwardNat _ _ _ _ AddCommGrpCat.{z} _
          (lisseEtaleInclusion X) (lisseEtaleTopology X) X.etaleTopology
          inferInstance inferInstance inferInstance inferInstance inferInstance
          (by
            have : HasLimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{z} :=
              hasLimitsOfSizeOfUnivLE AddCommGrpCat.{z}
            exact HasLimitsOfShape.of_small _ _)
          (by
            have : HasLimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{z} :=
              hasLimitsOfSizeOfUnivLE AddCommGrpCat.{z}
            exact HasLimitsOfShape.of_small _ _))

/-- Restriction of additive global sections of modules along the flat-fppf inclusion. -/
def flatFppfModuleGlobalSectionsComparison :
    moduleGlobalSectionsAdditiveFunctor.{z} (ringedSite X) ⟶
      (moduleInverseImage (J := flatFppfTopology X) (K := (inheritedFppfTopology X))
        (flatFppfInclusion X) (structureSheaf X)) ⋙
        moduleGlobalSectionsAdditiveFunctor.{z} (flatFppfRingedSite X) :=
  whiskerLeft (SheafOfModules.toSheaf (structureSheaf X))
    (@Sheaf.globalSectionsPushforwardNat _ _ _ _ AddCommGrpCat.{z} _
          (flatFppfInclusion X) (flatFppfTopology X) (inheritedFppfTopology X)
          inferInstance inferInstance inferInstance inferInstance inferInstance
          (by
            have : HasLimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{z} :=
              hasLimitsOfSizeOfUnivLE AddCommGrpCat.{z}
            exact HasLimitsOfShape.of_small _ _)
          (by
            have : HasLimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{z} :=
              hasLimitsOfSizeOfUnivLE AddCommGrpCat.{z}
            exact HasLimitsOfShape.of_small _ _))

/-- Homotopy-level exact-first unit for lisse-étale module inverse image
followed by additive global sections. -/
def lisseEtaleModuleDerivedGlobalSectionsExactFirstUnit :
    Functor.Homotopy.toDerived
        ((moduleInverseImage (J := lisseEtaleTopology X) (K := X.etaleTopology)
          (lisseEtaleInclusion X) (etaleStructureSheaf X)) ⋙
          moduleGlobalSectionsAdditiveFunctor.{z} (lisseEtaleRingedSite X)) ⟶
      (moduleLocalization.{z} (etaleRingedSite X)) ⋙
        (lisseEtaleInclusionDerivedInverseImage X ⋙
          moduleGlobalSectionsDerived.{z} (lisseEtaleRingedSite X)) :=
  (isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl
          ((moduleInverseImage (J := lisseEtaleTopology X) (K := X.etaleTopology)
            (lisseEtaleInclusion X) (etaleStructureSheaf X)) ⋙
            moduleGlobalSectionsAdditiveFunctor.{z} (lisseEtaleRingedSite X)))
        (up ℤ)).symm
      (DerivedCategory.Qh :
        HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
          DerivedCategory AddCommGrpCat.{z})).hom ≫
    (associator
        ((moduleInverseImage (J := lisseEtaleTopology X) (K := X.etaleTopology)
          (lisseEtaleInclusion X) (etaleStructureSheaf X)).mapHomotopyCategory (up ℤ))
        ((moduleGlobalSectionsAdditiveFunctor.{z}
            (lisseEtaleRingedSite X)).mapHomotopyCategory (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z})).hom ≫
    Composition.iteratedUnit
      (@Functor.mapDerivedCategoryFactorsh
        (RingedSite.ModuleCat.{z} (etaleRingedSite X)) inferInstance inferInstance
        (moduleCat_hasDerivedCategory.{z} (etaleRingedSite X))
        (RingedSite.ModuleCat.{z} (lisseEtaleRingedSite X)) inferInstance inferInstance
        (moduleCat_hasDerivedCategory.{z} (lisseEtaleRingedSite X))
        (moduleInverseImage.exactFunctor (J := lisseEtaleTopology X)
          (K := X.etaleTopology) (lisseEtaleInclusion X) (etaleStructureSheaf X)).obj
        inferInstance inferInstance inferInstance).inv
      (Homotopy.unit
        (moduleGlobalSectionsAdditiveFunctor.{z} (lisseEtaleRingedSite X)))

/-- Homotopy-level exact-first unit for flat-fppf module inverse image
followed by additive global sections. -/
def flatFppfModuleDerivedGlobalSectionsExactFirstUnit :
    Functor.Homotopy.toDerived
        ((moduleInverseImage (J := flatFppfTopology X) (K := (inheritedFppfTopology X))
          (flatFppfInclusion X) (structureSheaf X)) ⋙
          moduleGlobalSectionsAdditiveFunctor.{z} (flatFppfRingedSite X)) ⟶
      (moduleLocalization.{z} (ringedSite X)) ⋙
        (flatFppfInclusionDerivedInverseImage X ⋙
          moduleGlobalSectionsDerived.{z} (flatFppfRingedSite X)) :=
  (isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl
          ((moduleInverseImage (J := flatFppfTopology X) (K := (inheritedFppfTopology X))
            (flatFppfInclusion X) (structureSheaf X)) ⋙
            moduleGlobalSectionsAdditiveFunctor.{z} (flatFppfRingedSite X)))
        (up ℤ)).symm
      (DerivedCategory.Qh :
        HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
          DerivedCategory AddCommGrpCat.{z})).hom ≫
    (associator
        ((moduleInverseImage (J := flatFppfTopology X) (K := (inheritedFppfTopology X))
          (flatFppfInclusion X) (structureSheaf X)).mapHomotopyCategory (up ℤ))
        ((moduleGlobalSectionsAdditiveFunctor.{z}
            (flatFppfRingedSite X)).mapHomotopyCategory (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z})).hom ≫
    Composition.iteratedUnit
      (@Functor.mapDerivedCategoryFactorsh
        (RingedSite.ModuleCat.{z} (ringedSite X)) inferInstance inferInstance
        (moduleCat_hasDerivedCategory.{z} (ringedSite X))
        (RingedSite.ModuleCat.{z} (flatFppfRingedSite X)) inferInstance inferInstance
        (moduleCat_hasDerivedCategory.{z} (flatFppfRingedSite X))
        (moduleInverseImage.exactFunctor (J := flatFppfTopology X)
          (K := (inheritedFppfTopology X)) (flatFppfInclusion X) (structureSheaf X)).obj
        inferInstance inferInstance inferInstance).inv
      (Homotopy.unit
        (moduleGlobalSectionsAdditiveFunctor.{z} (flatFppfRingedSite X)))

/-- Canonical derived module comparison
`RΓ(X_étale, -) ⟶ RΓ(X_lisse,étale, -) ∘ g^*`. -/
def lisseEtaleModuleDerivedGlobalSectionsComparison :
    moduleGlobalSectionsDerived.{z} (etaleRingedSite X) ⟶
      lisseEtaleInclusionDerivedInverseImage X ⋙
        moduleGlobalSectionsDerived.{z} (lisseEtaleRingedSite X) :=
  (moduleGlobalSectionsDerived.{z} (etaleRingedSite X)).rightDerivedDesc
    (Functor.totalRightDerivedUnit
      (moduleGlobalSectionsToDerived.{z} (etaleRingedSite X))
      (moduleLocalization.{z} (etaleRingedSite X))
      (ModuleQis.{z} (etaleRingedSite X)))
    (ModuleQis.{z} (etaleRingedSite X))
    (lisseEtaleInclusionDerivedInverseImage X ⋙
      moduleGlobalSectionsDerived.{z} (lisseEtaleRingedSite X))
    (whiskerRight
        (NatTrans.mapHomotopyCategory
          (lisseEtaleModuleGlobalSectionsComparison X) (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z}) ≫
      lisseEtaleModuleDerivedGlobalSectionsExactFirstUnit X)

/-- Canonical derived module comparison
`RΓ(X_fppf, -) ⟶ RΓ(X_flat,fppf, -) ∘ g^*`. -/
def flatFppfModuleDerivedGlobalSectionsComparison :
    moduleGlobalSectionsDerived.{z} (ringedSite X) ⟶
      flatFppfInclusionDerivedInverseImage X ⋙
        moduleGlobalSectionsDerived.{z} (flatFppfRingedSite X) :=
  (moduleGlobalSectionsDerived.{z} (ringedSite X)).rightDerivedDesc
    (Functor.totalRightDerivedUnit
      (moduleGlobalSectionsToDerived.{z} (ringedSite X))
      (moduleLocalization.{z} (ringedSite X))
      (ModuleQis.{z} (ringedSite X)))
    (ModuleQis.{z} (ringedSite X))
    (flatFppfInclusionDerivedInverseImage X ⋙
      moduleGlobalSectionsDerived.{z} (flatFppfRingedSite X))
    (whiskerRight
        (NatTrans.mapHomotopyCategory
          (flatFppfModuleGlobalSectionsComparison X) (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z}) ≫
      flatFppfModuleDerivedGlobalSectionsExactFirstUnit X)

/-- Underived objectwise additive module-sections comparison along lisse-étale
inverse image, transported from the abelian `sectionsIso`. -/
def lisseEtaleModuleSectionsComparison (x : lisseEtaleSite X) :
    (moduleInverseImage (J := lisseEtaleTopology X) (K := X.etaleTopology)
      (lisseEtaleInclusion X) (etaleStructureSheaf X)) ⋙
        ModuleSections.Underlying.sections.{z} (lisseEtaleRingedSite X) x ⟶
      ModuleSections.Underlying.sections.{z} (etaleRingedSite X)
        ((lisseEtaleInclusion X).obj x) :=
  whiskerLeft (SheafOfModules.toSheaf (etaleStructureSheaf X))
    (SiteAbelianSectionsDerived.sectionsIso (lisseEtaleInclusion X) x).hom

/-- Underived objectwise additive module-sections comparison along flat-fppf
inverse image, transported from the abelian `sectionsIso`. -/
def flatFppfModuleSectionsComparison (x : flatFppfSite X) :
    (moduleInverseImage (J := flatFppfTopology X) (K := (inheritedFppfTopology X))
      (flatFppfInclusion X) (structureSheaf X)) ⋙
        ModuleSections.Underlying.sections.{z} (flatFppfRingedSite X) x ⟶
      ModuleSections.Underlying.sections.{z} (ringedSite X)
        ((flatFppfInclusion X).obj x) :=
  whiskerLeft (SheafOfModules.toSheaf (structureSheaf X))
    (SiteAbelianSectionsDerived.sectionsIso (flatFppfInclusion X) x).hom

/-- Homotopy-level exact-first unit for lisse-étale module inverse image
followed by objectwise additive sections. -/
def lisseEtaleModuleDerivedSectionsExactFirstUnit (x : lisseEtaleSite X) :
    Functor.Homotopy.toDerived
        ((moduleInverseImage (J := lisseEtaleTopology X) (K := X.etaleTopology)
          (lisseEtaleInclusion X) (etaleStructureSheaf X)) ⋙
          ModuleSections.Underlying.sections.{z} (lisseEtaleRingedSite X) x) ⟶
      (moduleLocalization.{z} (etaleRingedSite X)) ⋙
        (lisseEtaleInclusionDerivedInverseImage X ⋙
          ModuleSections.Underlying.sectionsDerived.{z}
            (lisseEtaleRingedSite X) x) :=
  (isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl
          ((moduleInverseImage (J := lisseEtaleTopology X) (K := X.etaleTopology)
            (lisseEtaleInclusion X) (etaleStructureSheaf X)) ⋙
            ModuleSections.Underlying.sections.{z} (lisseEtaleRingedSite X)
              x))
        (up ℤ)).symm
      (DerivedCategory.Qh :
        HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
          DerivedCategory AddCommGrpCat.{z})).hom ≫
    (associator
        ((moduleInverseImage (J := lisseEtaleTopology X) (K := X.etaleTopology)
          (lisseEtaleInclusion X) (etaleStructureSheaf X)).mapHomotopyCategory (up ℤ))
        ((ModuleSections.Underlying.sections.{z} (lisseEtaleRingedSite X)
            x).mapHomotopyCategory (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z})).hom ≫
    Composition.iteratedUnit
      (@Functor.mapDerivedCategoryFactorsh
        (RingedSite.ModuleCat.{z} (etaleRingedSite X)) inferInstance inferInstance
        (moduleCat_hasDerivedCategory.{z} (etaleRingedSite X))
        (RingedSite.ModuleCat.{z} (lisseEtaleRingedSite X)) inferInstance inferInstance
        (moduleCat_hasDerivedCategory.{z} (lisseEtaleRingedSite X))
        (moduleInverseImage.exactFunctor (J := lisseEtaleTopology X)
          (K := X.etaleTopology) (lisseEtaleInclusion X) (etaleStructureSheaf X)).obj
        inferInstance inferInstance inferInstance).inv
      (Homotopy.unit
        (ModuleSections.Underlying.sections.{z} (lisseEtaleRingedSite X) x))

/-- Homotopy-level exact-first unit for flat-fppf module inverse image
followed by objectwise additive sections. -/
def flatFppfModuleDerivedSectionsExactFirstUnit (x : flatFppfSite X) :
    Functor.Homotopy.toDerived
        ((moduleInverseImage (J := flatFppfTopology X) (K := (inheritedFppfTopology X))
          (flatFppfInclusion X) (structureSheaf X)) ⋙
          ModuleSections.Underlying.sections.{z} (flatFppfRingedSite X) x) ⟶
      (moduleLocalization.{z} (ringedSite X)) ⋙
        (flatFppfInclusionDerivedInverseImage X ⋙
          ModuleSections.Underlying.sectionsDerived.{z}
            (flatFppfRingedSite X) x) :=
  (isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl
          ((moduleInverseImage (J := flatFppfTopology X) (K := (inheritedFppfTopology X))
            (flatFppfInclusion X) (structureSheaf X)) ⋙
            ModuleSections.Underlying.sections.{z} (flatFppfRingedSite X)
              x))
        (up ℤ)).symm
      (DerivedCategory.Qh :
        HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
          DerivedCategory AddCommGrpCat.{z})).hom ≫
    (associator
        ((moduleInverseImage (J := flatFppfTopology X) (K := (inheritedFppfTopology X))
          (flatFppfInclusion X) (structureSheaf X)).mapHomotopyCategory (up ℤ))
        ((ModuleSections.Underlying.sections.{z} (flatFppfRingedSite X)
            x).mapHomotopyCategory (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z})).hom ≫
    Composition.iteratedUnit
      (@Functor.mapDerivedCategoryFactorsh
        (RingedSite.ModuleCat.{z} (ringedSite X)) inferInstance inferInstance
        (moduleCat_hasDerivedCategory.{z} (ringedSite X))
        (RingedSite.ModuleCat.{z} (flatFppfRingedSite X)) inferInstance inferInstance
        (moduleCat_hasDerivedCategory.{z} (flatFppfRingedSite X))
        (moduleInverseImage.exactFunctor (J := flatFppfTopology X)
          (K := (inheritedFppfTopology X)) (flatFppfInclusion X) (structureSheaf X)).obj
        inferInstance inferInstance inferInstance).inv
      (Homotopy.unit
        (ModuleSections.Underlying.sections.{z} (flatFppfRingedSite X) x))

/-- Exact derived lisse-étale module inverse image followed by objectwise
derived additive sections is a right-derived functor of the underived
composite. -/
instance lisseEtaleModuleInverseImageDerived_comp_sections_isRightDerived
    (x : lisseEtaleSite X) :
    (lisseEtaleInclusionDerivedInverseImage X ⋙
        ModuleSections.Underlying.sectionsDerived.{z}
          (lisseEtaleRingedSite X) x).IsRightDerivedFunctor
      (lisseEtaleModuleDerivedSectionsExactFirstUnit X x)
      (ModuleQis.{z} (etaleRingedSite X)) :=
  sorry

/-- Exact derived flat-fppf module inverse image followed by objectwise
derived additive sections is a right-derived functor of the underived
composite. -/
instance flatFppfModuleInverseImageDerived_comp_sections_isRightDerived
    (x : flatFppfSite X) :
    (flatFppfInclusionDerivedInverseImage X ⋙
        ModuleSections.Underlying.sectionsDerived.{z}
          (flatFppfRingedSite X) x).IsRightDerivedFunctor
      (flatFppfModuleDerivedSectionsExactFirstUnit X x)
      (ModuleQis.{z} (ringedSite X)) :=
  sorry

/-- Canonical derived module comparison
`RΓ(X_lisse,étale/x, g^* -) ⟶ RΓ(x, -)`. -/
def lisseEtaleModuleDerivedSectionsComparison (x : lisseEtaleSite X) :
    lisseEtaleInclusionDerivedInverseImage X ⋙
        ModuleSections.Underlying.sectionsDerived.{z}
          (lisseEtaleRingedSite X) x ⟶
      ModuleSections.Underlying.sectionsDerived.{z} (etaleRingedSite X)
        ((lisseEtaleInclusion X).obj x) :=
  (lisseEtaleInclusionDerivedInverseImage X ⋙
      ModuleSections.Underlying.sectionsDerived.{z}
        (lisseEtaleRingedSite X) x).rightDerivedDesc
    (lisseEtaleModuleDerivedSectionsExactFirstUnit X x)
    (ModuleQis.{z} (etaleRingedSite X))
    (ModuleSections.Underlying.sectionsDerived.{z} (etaleRingedSite X)
      ((lisseEtaleInclusion X).obj x))
    (whiskerRight
        (NatTrans.mapHomotopyCategory
          (lisseEtaleModuleSectionsComparison X x) (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z}) ≫
      Homotopy.unit
        (ModuleSections.Underlying.sections.{z} (etaleRingedSite X)
          ((lisseEtaleInclusion X).obj x)))

/-- Canonical derived module comparison
`RΓ(X_flat,fppf/x, g^* -) ⟶ RΓ(x, -)`. -/
def flatFppfModuleDerivedSectionsComparison (x : flatFppfSite X) :
    flatFppfInclusionDerivedInverseImage X ⋙
        ModuleSections.Underlying.sectionsDerived.{z}
          (flatFppfRingedSite X) x ⟶
      ModuleSections.Underlying.sectionsDerived.{z} (ringedSite X)
        ((flatFppfInclusion X).obj x) :=
  (flatFppfInclusionDerivedInverseImage X ⋙
      ModuleSections.Underlying.sectionsDerived.{z}
        (flatFppfRingedSite X) x).rightDerivedDesc
    (flatFppfModuleDerivedSectionsExactFirstUnit X x)
    (ModuleQis.{z} (ringedSite X))
    (ModuleSections.Underlying.sectionsDerived.{z} (ringedSite X)
      ((flatFppfInclusion X).obj x))
    (whiskerRight
        (NatTrans.mapHomotopyCategory
          (flatFppfModuleSectionsComparison X x) (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z}) ≫
      Homotopy.unit
        (ModuleSections.Underlying.sections.{z} (ringedSite X)
          ((flatFppfInclusion X).obj x)))

/-- The canonical lisse-étale derived global sections comparison for module coefficients is
invertible. -/
@[stacks 0H10]
instance lisseEtaleModuleDerivedGlobalSectionsComparison.instIsIso :
    IsIso (lisseEtaleModuleDerivedGlobalSectionsComparison X) := sorry

/-- The canonical lisse-étale derived objectwise sections comparison for module coefficients is
invertible. -/
@[stacks 0H10]
instance lisseEtaleModuleDerivedSectionsComparison.instIsIso
    (x : lisseEtaleSite X) :
    IsIso (lisseEtaleModuleDerivedSectionsComparison X x) := sorry

/-- The canonical flat-fppf derived global sections comparison for module coefficients is
invertible. -/
@[stacks 0H10]
instance flatFppfModuleDerivedGlobalSectionsComparison.instIsIso :
    IsIso (flatFppfModuleDerivedGlobalSectionsComparison X) := sorry

/-- The canonical flat-fppf derived objectwise sections comparison for module coefficients is
invertible. -/
@[stacks 0H10]
instance flatFppfModuleDerivedSectionsComparison.instIsIso
    (x : flatFppfSite X) :
    IsIso (flatFppfModuleDerivedSectionsComparison X x) := sorry

/-- The derived comparison factors its defining localization unit. -/
lemma lisseEtaleModuleDerivedGlobalSectionsComparison_fac :
    (Functor.totalRightDerivedUnit
      (moduleGlobalSectionsToDerived.{z} (etaleRingedSite X))
      (moduleLocalization.{z} (etaleRingedSite X))
      (ModuleQis.{z} (etaleRingedSite X))) ≫
      whiskerLeft (moduleLocalization.{z} (etaleRingedSite X))
        (lisseEtaleModuleDerivedGlobalSectionsComparison X) =
    (whiskerRight
        (NatTrans.mapHomotopyCategory
          (lisseEtaleModuleGlobalSectionsComparison X) (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z}) ≫
      lisseEtaleModuleDerivedGlobalSectionsExactFirstUnit X) := by
  exact (moduleGlobalSectionsDerived.{z} (etaleRingedSite X)).rightDerived_fac
    (Functor.totalRightDerivedUnit
      (moduleGlobalSectionsToDerived.{z} (etaleRingedSite X))
      (moduleLocalization.{z} (etaleRingedSite X))
      (ModuleQis.{z} (etaleRingedSite X)))
    (ModuleQis.{z} (etaleRingedSite X))
    (lisseEtaleInclusionDerivedInverseImage X ⋙
      moduleGlobalSectionsDerived.{z} (lisseEtaleRingedSite X))
    (whiskerRight
        (NatTrans.mapHomotopyCategory
          (lisseEtaleModuleGlobalSectionsComparison X) (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z}) ≫
      lisseEtaleModuleDerivedGlobalSectionsExactFirstUnit X)

/-- The derived comparison factors its defining localization unit. -/
lemma flatFppfModuleDerivedGlobalSectionsComparison_fac :
    (Functor.totalRightDerivedUnit
      (moduleGlobalSectionsToDerived.{z} (ringedSite X))
      (moduleLocalization.{z} (ringedSite X))
      (ModuleQis.{z} (ringedSite X))) ≫
      whiskerLeft (moduleLocalization.{z} (ringedSite X))
        (flatFppfModuleDerivedGlobalSectionsComparison X) =
    (whiskerRight
        (NatTrans.mapHomotopyCategory
          (flatFppfModuleGlobalSectionsComparison X) (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z}) ≫
      flatFppfModuleDerivedGlobalSectionsExactFirstUnit X) := by
  exact (moduleGlobalSectionsDerived.{z} (ringedSite X)).rightDerived_fac
    (Functor.totalRightDerivedUnit
      (moduleGlobalSectionsToDerived.{z} (ringedSite X))
      (moduleLocalization.{z} (ringedSite X))
      (ModuleQis.{z} (ringedSite X)))
    (ModuleQis.{z} (ringedSite X))
    (flatFppfInclusionDerivedInverseImage X ⋙
      moduleGlobalSectionsDerived.{z} (flatFppfRingedSite X))
    (whiskerRight
        (NatTrans.mapHomotopyCategory
          (flatFppfModuleGlobalSectionsComparison X) (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z}) ≫
      flatFppfModuleDerivedGlobalSectionsExactFirstUnit X)

/-- The derived comparison factors its defining localization unit. -/
lemma lisseEtaleModuleDerivedSectionsComparison_fac (x : lisseEtaleSite X) :
    (lisseEtaleModuleDerivedSectionsExactFirstUnit X x) ≫
      whiskerLeft (moduleLocalization.{z} (etaleRingedSite X))
        (lisseEtaleModuleDerivedSectionsComparison X x) =
    (whiskerRight
        (NatTrans.mapHomotopyCategory
          (lisseEtaleModuleSectionsComparison X x) (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z}) ≫
      Homotopy.unit
        (ModuleSections.Underlying.sections.{z} (etaleRingedSite X)
          ((lisseEtaleInclusion X).obj x))) := by
  exact (lisseEtaleInclusionDerivedInverseImage X ⋙
      ModuleSections.Underlying.sectionsDerived.{z}
        (lisseEtaleRingedSite X) x).rightDerived_fac
    (lisseEtaleModuleDerivedSectionsExactFirstUnit X x)
    (ModuleQis.{z} (etaleRingedSite X))
    (ModuleSections.Underlying.sectionsDerived.{z} (etaleRingedSite X)
      ((lisseEtaleInclusion X).obj x))
    (whiskerRight
        (NatTrans.mapHomotopyCategory
          (lisseEtaleModuleSectionsComparison X x) (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z}) ≫
      Homotopy.unit
        (ModuleSections.Underlying.sections.{z} (etaleRingedSite X)
          ((lisseEtaleInclusion X).obj x)))

/-- The derived comparison factors its defining localization unit. -/
lemma flatFppfModuleDerivedSectionsComparison_fac (x : flatFppfSite X) :
    (flatFppfModuleDerivedSectionsExactFirstUnit X x) ≫
      whiskerLeft (moduleLocalization.{z} (ringedSite X))
        (flatFppfModuleDerivedSectionsComparison X x) =
    (whiskerRight
        (NatTrans.mapHomotopyCategory
          (flatFppfModuleSectionsComparison X x) (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z}) ≫
      Homotopy.unit
        (ModuleSections.Underlying.sections.{z} (ringedSite X)
          ((flatFppfInclusion X).obj x))) := by
  exact (flatFppfInclusionDerivedInverseImage X ⋙
      ModuleSections.Underlying.sectionsDerived.{z}
        (flatFppfRingedSite X) x).rightDerived_fac
    (flatFppfModuleDerivedSectionsExactFirstUnit X x)
    (ModuleQis.{z} (ringedSite X))
    (ModuleSections.Underlying.sectionsDerived.{z} (ringedSite X)
      ((flatFppfInclusion X).obj x))
    (whiskerRight
        (NatTrans.mapHomotopyCategory
          (flatFppfModuleSectionsComparison X x) (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z}) ≫
      Homotopy.unit
        (ModuleSections.Underlying.sections.{z} (ringedSite X)
          ((flatFppfInclusion X).obj x)))

end AlgebraicGeometry.AlgebraicStack
