module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Underlying
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.Sites.Derived.SectionsComparison
public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive
public import stacks_project.Chap104.Lemma_104_3_1_Module
public import stacks_project.Chap104.Lemma_104_4_1
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 104.4.2

Derived global and objectwise sections on an algebraic stack are unchanged after
inverse image along the lisse-étale and flat-fppf inclusions of Lemma 104.3.1.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Functor CategoryTheory.Limits ComplexShape
open RingedSite.Hom
open Functor.RightDerived

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
variable [UnivLE.{u + 1, z}]

/-- Abelian sheaves on the associated étale site form a Grothendieck abelian
category. -/
instance etaleTopology_isGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.etaleTopology AddCommGrpCat.{z}) :=
  sorry

/-- Abelian sheaves on the lisse-étale site form a Grothendieck abelian
category. -/
instance lisseEtaleTopology_isGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1} (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z}) :=
  sorry

/-- Abelian sheaves on the inherited fppf site form a Grothendieck abelian
category. -/
instance inheritedFppfTopology_isGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1} (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) :=
  sorry

/-- Abelian sheaves on the flat-fppf site form a Grothendieck abelian category. -/
instance flatFppfTopology_isGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1} (Sheaf (flatFppfTopology X) AddCommGrpCat.{z}) :=
  sorry

/-- The associated étale site admits abelian global sections. -/
instance etaleTopology_hasGlobalSectionsFunctor :
    HasGlobalSectionsFunctor X.etaleTopology AddCommGrpCat.{z} := sorry

/-- The lisse-étale site admits abelian global sections. -/
instance lisseEtaleTopology_hasGlobalSectionsFunctor :
    HasGlobalSectionsFunctor (lisseEtaleTopology X) AddCommGrpCat.{z} :=
  sorry

/-- The inherited fppf site admits abelian global sections. -/
instance inheritedFppfTopology_hasGlobalSectionsFunctor :
    HasGlobalSectionsFunctor (inheritedFppfTopology X) AddCommGrpCat.{z} :=
  sorry

/-- The flat-fppf site admits abelian global sections. -/
instance flatFppfTopology_hasGlobalSectionsFunctor :
    HasGlobalSectionsFunctor (flatFppfTopology X) AddCommGrpCat.{z} := sorry

/-- Modules on the associated étale ringed site form a Grothendieck abelian
category. -/
instance etaleModules_isGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1}
      (RingedSite.ModuleCat.{z}
        (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X))) :=
  sorry

/-- Modules on the lisse-étale ringed site form a Grothendieck abelian
category. -/
instance lisseEtaleModules_isGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1}
      (RingedSite.ModuleCat.{z} (lisseEtaleRingedSite X)) :=
  sorry

/-- Modules on the inherited fppf ringed site form a Grothendieck abelian
category. -/
instance inheritedFppfModules_isGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1}
      (RingedSite.ModuleCat.{z} (ringedSite X)) := sorry

/-- Modules on the flat-fppf ringed site form a Grothendieck abelian category. -/
instance flatFppfModules_isGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1}
      (RingedSite.ModuleCat.{z} (flatFppfRingedSite X)) :=
  sorry

/-- Continuous inverse image of abelian sheaves along the lisse-étale
inclusion. -/
abbrev lisseEtaleAbelianInverseImage :
    Sheaf X.etaleTopology AddCommGrpCat.{z} ⥤
      Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z} :=
  (lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
    (lisseEtaleTopology X) X.etaleTopology

/-- Continuous inverse image of abelian sheaves along the flat-fppf
inclusion. -/
abbrev flatFppfAbelianInverseImage :
    Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z} ⥤
      Sheaf (flatFppfTopology X) AddCommGrpCat.{z} :=
  (flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
    (flatFppfTopology X) (inheritedFppfTopology X)

/-- The étale ringed site of `X` at coefficient universe `z`. -/
abbrev etaleRingedSiteCoeff : RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)

/-- Underived comparison `Γ(X_étale, F) ⟶ Γ(X_lisse,étale, g⁻¹ F)` induced by
the adjoint form `ℤ ⟶ g⁻¹ ℤ` of the Lemma 104.4.1 identification
`Lg_! ℤ ≅ ℤ`. -/
def lisseEtaleAbelianGlobalSectionsComparison :
    Sheaf.Γ X.etaleTopology AddCommGrpCat.{z} ⟶
      lisseEtaleAbelianInverseImage X ⋙
        Sheaf.Γ (lisseEtaleTopology X) AddCommGrpCat.{z} where
  app F :=
    AddCommGrpCat.ofHom
      (AddMonoidHom.mk'
        (fun x ↦
          (Sheaf.globalSectionsAddEquivConstantIntegerSheafHomOnSite
                (lisseEtaleTopology X)
                ((lisseEtaleAbelianInverseImage X).obj F)).symm
            (lisseEtaleInverseImage_constantInteger_hom X ≫
              (lisseEtaleAbelianInverseImage X).map
                ((Sheaf.globalSectionsAddEquivConstantIntegerSheafHomOnSite
                    X.etaleTopology F) x)))
        sorry)
  naturality _ _ _ := sorry

/-- Underived comparison `Γ(X_fppf, F) ⟶ Γ(X_flat,fppf, g⁻¹ F)` induced by
the adjoint form `ℤ ⟶ g⁻¹ ℤ` of the Lemma 104.4.1 identification
`Lg_! ℤ ≅ ℤ`. -/
def flatFppfAbelianGlobalSectionsComparison :
    Sheaf.Γ (inheritedFppfTopology X) AddCommGrpCat.{z} ⟶
      flatFppfAbelianInverseImage X ⋙
        Sheaf.Γ (flatFppfTopology X) AddCommGrpCat.{z} where
  app F :=
    AddCommGrpCat.ofHom
      (AddMonoidHom.mk'
        (fun x ↦
          (Sheaf.globalSectionsAddEquivConstantIntegerSheafHomOnSite
                (flatFppfTopology X)
                ((flatFppfAbelianInverseImage X).obj F)).symm
            (flatFppfInverseImage_constantInteger_hom X ≫
              (flatFppfAbelianInverseImage X).map
                ((Sheaf.globalSectionsAddEquivConstantIntegerSheafHomOnSite
                    (inheritedFppfTopology X) F) x)))
        sorry)
  naturality _ _ _ := sorry

/-- Cochain-level unit of the underived lisse-étale global comparison, composed
with the exact-first unit of derived inverse image. -/
def lisseEtaleAbelianDerivedGlobalSectionsUnit :
    Cochain.toDerived (Sheaf.Γ X.etaleTopology AddCommGrpCat.{z}) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{z}) ℤ ⥤
            DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{z})) ⋙
        (lisseEtaleAbelianInverseImageDerived X ⋙
          Cochain.functor (Sheaf.Γ (lisseEtaleTopology X) AddCommGrpCat.{z})) :=
  whiskerRight
      (NatTrans.mapHomologicalComplex
        (lisseEtaleAbelianGlobalSectionsComparison X) (up ℤ))
      (DerivedCategory.Q :
        CochainComplex AddCommGrpCat.{z} ℤ ⥤ DerivedCategory AddCommGrpCat.{z}) ≫
    Cochain.ExactFirst.unit
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
        (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X))
      (Sheaf.Γ (lisseEtaleTopology X) AddCommGrpCat.{z})

/-- Cochain-level unit of the underived flat-fppf global comparison, composed
with the exact-first unit of derived inverse image. -/
def flatFppfAbelianDerivedGlobalSectionsUnit :
    Cochain.toDerived (Sheaf.Γ (inheritedFppfTopology X) AddCommGrpCat.{z}) ⟶
      (DerivedCategory.Q :
          CochainComplex
              (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) ℤ ⥤
            DerivedCategory
              (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z})) ⋙
        (flatFppfAbelianInverseImageDerived X ⋙
          Cochain.functor (Sheaf.Γ (flatFppfTopology X) AddCommGrpCat.{z})) :=
  whiskerRight
      (NatTrans.mapHomologicalComplex
        (flatFppfAbelianGlobalSectionsComparison X) (up ℤ))
      (DerivedCategory.Q :
        CochainComplex AddCommGrpCat.{z} ℤ ⥤ DerivedCategory AddCommGrpCat.{z}) ≫
    Cochain.ExactFirst.unit
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
        (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X))
      (Sheaf.Γ (flatFppfTopology X) AddCommGrpCat.{z})

/-- Canonical derived comparison
`RΓ(X_étale, -) ⟶ RΓ(X_lisse,étale, -) ∘ g⁻¹`, obtained from the
Hom(ℤ, -) comparison of Lemma 104.4.1 by derived uniqueness and the
exact-first unit of `lisseEtaleAbelianInverseImageDerived`. -/
def lisseEtaleAbelianDerivedGlobalSectionsComparison :
    Cochain.functor (Sheaf.Γ X.etaleTopology AddCommGrpCat.{z}) ⟶
      lisseEtaleAbelianInverseImageDerived X ⋙
        Cochain.functor (Sheaf.Γ (lisseEtaleTopology X) AddCommGrpCat.{z}) :=
  (Cochain.functor (Sheaf.Γ X.etaleTopology AddCommGrpCat.{z})).rightDerivedDesc
    (Cochain.unit (Sheaf.Γ X.etaleTopology AddCommGrpCat.{z}))
    (HomologicalComplex.quasiIso
      (Sheaf X.etaleTopology AddCommGrpCat.{z}) (up ℤ))
    (lisseEtaleAbelianInverseImageDerived X ⋙
      Cochain.functor (Sheaf.Γ (lisseEtaleTopology X) AddCommGrpCat.{z}))
    (lisseEtaleAbelianDerivedGlobalSectionsUnit X)

/-- Canonical derived comparison
`RΓ(X_fppf, -) ⟶ RΓ(X_flat,fppf, -) ∘ g⁻¹`, obtained from the
Hom(ℤ, -) comparison of Lemma 104.4.1 by derived uniqueness and the
exact-first unit of `flatFppfAbelianInverseImageDerived`. -/
def flatFppfAbelianDerivedGlobalSectionsComparison :
    Cochain.functor (Sheaf.Γ (inheritedFppfTopology X) AddCommGrpCat.{z}) ⟶
      flatFppfAbelianInverseImageDerived X ⋙
        Cochain.functor (Sheaf.Γ (flatFppfTopology X) AddCommGrpCat.{z}) :=
  (Cochain.functor
      (Sheaf.Γ (inheritedFppfTopology X) AddCommGrpCat.{z})).rightDerivedDesc
    (Cochain.unit (Sheaf.Γ (inheritedFppfTopology X) AddCommGrpCat.{z}))
    (HomologicalComplex.quasiIso
      (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) (up ℤ))
    (flatFppfAbelianInverseImageDerived X ⋙
      Cochain.functor (Sheaf.Γ (flatFppfTopology X) AddCommGrpCat.{z}))
    (flatFppfAbelianDerivedGlobalSectionsUnit X)

/-- Exact derived lisse-étale inverse image followed by objectwise derived
sections is a right-derived functor of the underived composite. -/
instance lisseEtaleAbelianInverseImageDerived_comp_sections_isRightDerived
    (x : lisseEtaleSite X) :
    (lisseEtaleAbelianInverseImageDerived X ⋙
        siteAbelianSectionsDerived (lisseEtaleTopology X) x).IsRightDerivedFunctor
      (Cochain.ExactFirst.unit
        (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
          (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X))
        (siteAbelianSectionsFunctor (lisseEtaleTopology X) x))
      (HomologicalComplex.quasiIso
        (Sheaf X.etaleTopology AddCommGrpCat.{z}) (up ℤ)) :=
  sorry

/-- Exact derived flat-fppf inverse image followed by objectwise derived
sections is a right-derived functor of the underived composite. -/
instance flatFppfAbelianInverseImageDerived_comp_sections_isRightDerived
    (x : flatFppfSite X) :
    (flatFppfAbelianInverseImageDerived X ⋙
        siteAbelianSectionsDerived (flatFppfTopology X) x).IsRightDerivedFunctor
      (Cochain.ExactFirst.unit
        (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
          (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X))
        (siteAbelianSectionsFunctor (flatFppfTopology X) x))
      (HomologicalComplex.quasiIso
        (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) (up ℤ)) :=
  sorry

/-- Canonical derived comparison
`RΓ(X_lisse,étale/x, g⁻¹ -) ⟶ RΓ(x, -)` for `x` in the lisse-étale
site, using `sectionsToDerivedIso` and the exact-first unit. -/
def lisseEtaleAbelianDerivedSectionsComparison (x : lisseEtaleSite X) :
    lisseEtaleAbelianInverseImageDerived X ⋙
        siteAbelianSectionsDerived (lisseEtaleTopology X) x ⟶
      siteAbelianSectionsDerived X.etaleTopology
        ((lisseEtaleInclusion X).obj x) :=
  rightDerivedNatTrans
    (lisseEtaleAbelianInverseImageDerived X ⋙
      siteAbelianSectionsDerived (lisseEtaleTopology X) x)
    (siteAbelianSectionsDerived X.etaleTopology
      ((lisseEtaleInclusion X).obj x))
    (Cochain.ExactFirst.unit
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
        (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X))
      (siteAbelianSectionsFunctor (lisseEtaleTopology X) x))
    ((Cochain.toDerived
        (siteAbelianSectionsFunctor X.etaleTopology
          ((lisseEtaleInclusion X).obj x))).totalRightDerivedUnit
      (DerivedCategory.Q :
        CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{z}) ℤ ⥤
          DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{z}))
      (HomologicalComplex.quasiIso
        (Sheaf X.etaleTopology AddCommGrpCat.{z}) (up ℤ)))
    (HomologicalComplex.quasiIso
      (Sheaf X.etaleTopology AddCommGrpCat.{z}) (up ℤ))
    (SiteAbelianSectionsDerived.sectionsToDerivedIso
      (lisseEtaleInclusion X) x).hom

/-- Canonical derived comparison
`RΓ(X_flat,fppf/x, g⁻¹ -) ⟶ RΓ(x, -)` for `x` in the flat-fppf site,
using `sectionsToDerivedIso` and the exact-first unit. -/
def flatFppfAbelianDerivedSectionsComparison (x : flatFppfSite X) :
    flatFppfAbelianInverseImageDerived X ⋙
        siteAbelianSectionsDerived (flatFppfTopology X) x ⟶
      siteAbelianSectionsDerived (inheritedFppfTopology X)
        ((flatFppfInclusion X).obj x) :=
  rightDerivedNatTrans
    (flatFppfAbelianInverseImageDerived X ⋙
      siteAbelianSectionsDerived (flatFppfTopology X) x)
    (siteAbelianSectionsDerived (inheritedFppfTopology X)
      ((flatFppfInclusion X).obj x))
    (Cochain.ExactFirst.unit
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
        (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X))
      (siteAbelianSectionsFunctor (flatFppfTopology X) x))
    ((Cochain.toDerived
        (siteAbelianSectionsFunctor (inheritedFppfTopology X)
          ((flatFppfInclusion X).obj x))).totalRightDerivedUnit
      (DerivedCategory.Q :
        CochainComplex
            (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) ℤ ⥤
          DerivedCategory
            (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}))
      (HomologicalComplex.quasiIso
        (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) (up ℤ)))
    (HomologicalComplex.quasiIso
      (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) (up ℤ))
    (SiteAbelianSectionsDerived.sectionsToDerivedIso
      (flatFppfInclusion X) x).hom

/-- Underived additive module global-sections comparison along lisse-étale
inverse image, obtained by applying the abelian Hom(ℤ, -) comparison after
forgetting scalars. -/
def lisseEtaleModuleGlobalSectionsComparison :
    moduleGlobalSectionsAdditiveFunctor.{z} (etaleRingedSiteCoeff X) ⟶
      lisseEtaleModuleInverseImageCoeff X ⋙
        moduleGlobalSectionsAdditiveFunctor.{z} (lisseEtaleRingedSite X) where
  app M :=
    (lisseEtaleAbelianGlobalSectionsComparison X).app
      ((SheafOfModules.toSheaf (etaleStructureSheaf X)).obj M)
  naturality _ _ _ := sorry

/-- Underived additive module global-sections comparison along flat-fppf
inverse image, obtained by applying the abelian Hom(ℤ, -) comparison after
forgetting scalars. -/
def flatFppfModuleGlobalSectionsComparison :
    moduleGlobalSectionsAdditiveFunctor.{z} (ringedSite X) ⟶
      flatFppfModuleInverseImageCoeff X ⋙
        moduleGlobalSectionsAdditiveFunctor.{z} (flatFppfRingedSite X) where
  app M :=
    (flatFppfAbelianGlobalSectionsComparison X).app
      ((SheafOfModules.toSheaf (structureSheaf X)).obj M)
  naturality _ _ _ := sorry

/-- Homotopy-level exact-first unit for lisse-étale module inverse image
followed by additive global sections. -/
def lisseEtaleModuleDerivedGlobalSectionsExactFirstUnit :
    Functor.Homotopy.toDerived
        (lisseEtaleModuleInverseImageCoeff X ⋙
          moduleGlobalSectionsAdditiveFunctor.{z} (lisseEtaleRingedSite X)) ⟶
      (DerivedCategory.Qh :
          HomotopyCategory
              (RingedSite.ModuleCat.{z} (etaleRingedSiteCoeff X)) (up ℤ) ⥤
            RingedSite.Hom.ModuleDerived.{z} (etaleRingedSiteCoeff X)) ⋙
        (lisseEtaleModuleInverseImageDerived X ⋙
          moduleGlobalSectionsDerived.{z} (lisseEtaleRingedSite X)) :=
  (isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl
          (lisseEtaleModuleInverseImageCoeff X ⋙
            moduleGlobalSectionsAdditiveFunctor.{z} (lisseEtaleRingedSite X)))
        (up ℤ)).symm
      (DerivedCategory.Qh :
        HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
          DerivedCategory AddCommGrpCat.{z})).hom ≫
    (associator
        ((lisseEtaleModuleInverseImageCoeff X).mapHomotopyCategory (up ℤ))
        ((moduleGlobalSectionsAdditiveFunctor.{z}
            (lisseEtaleRingedSite X)).mapHomotopyCategory (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z})).hom ≫
    Composition.iteratedUnit
      (lisseEtaleModuleInverseImageExact X).obj.mapDerivedCategoryFactorsh.inv
      (Homotopy.unit
        (moduleGlobalSectionsAdditiveFunctor.{z} (lisseEtaleRingedSite X)))

/-- Homotopy-level exact-first unit for flat-fppf module inverse image
followed by additive global sections. -/
def flatFppfModuleDerivedGlobalSectionsExactFirstUnit :
    Functor.Homotopy.toDerived
        (flatFppfModuleInverseImageCoeff X ⋙
          moduleGlobalSectionsAdditiveFunctor.{z} (flatFppfRingedSite X)) ⟶
      (DerivedCategory.Qh :
          HomotopyCategory (RingedSite.ModuleCat.{z} (ringedSite X)) (up ℤ) ⥤
            RingedSite.Hom.ModuleDerived.{z} (ringedSite X)) ⋙
        (flatFppfModuleInverseImageDerived X ⋙
          moduleGlobalSectionsDerived.{z} (flatFppfRingedSite X)) :=
  (isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl
          (flatFppfModuleInverseImageCoeff X ⋙
            moduleGlobalSectionsAdditiveFunctor.{z} (flatFppfRingedSite X)))
        (up ℤ)).symm
      (DerivedCategory.Qh :
        HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
          DerivedCategory AddCommGrpCat.{z})).hom ≫
    (associator
        ((flatFppfModuleInverseImageCoeff X).mapHomotopyCategory (up ℤ))
        ((moduleGlobalSectionsAdditiveFunctor.{z}
            (flatFppfRingedSite X)).mapHomotopyCategory (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z})).hom ≫
    Composition.iteratedUnit
      (flatFppfModuleInverseImageExact X).obj.mapDerivedCategoryFactorsh.inv
      (Homotopy.unit
        (moduleGlobalSectionsAdditiveFunctor.{z} (flatFppfRingedSite X)))

/-- Canonical derived module comparison
`RΓ(X_étale, -) ⟶ RΓ(X_lisse,étale, -) ∘ g^*`. -/
def lisseEtaleModuleDerivedGlobalSectionsComparison :
    moduleGlobalSectionsDerived.{z} (etaleRingedSiteCoeff X) ⟶
      lisseEtaleModuleInverseImageDerived X ⋙
        moduleGlobalSectionsDerived.{z} (lisseEtaleRingedSite X) :=
  (moduleGlobalSectionsDerived.{z} (etaleRingedSiteCoeff X)).rightDerivedDesc
    (Functor.totalRightDerivedUnit
      (moduleGlobalSectionsToDerived.{z} (etaleRingedSiteCoeff X))
      (DerivedCategory.Qh :
        HomotopyCategory
            (RingedSite.ModuleCat.{z} (etaleRingedSiteCoeff X)) (up ℤ) ⥤
          RingedSite.Hom.ModuleDerived.{z} (etaleRingedSiteCoeff X))
      (ModuleQis.{z} (etaleRingedSiteCoeff X)))
    (ModuleQis.{z} (etaleRingedSiteCoeff X))
    (lisseEtaleModuleInverseImageDerived X ⋙
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
      flatFppfModuleInverseImageDerived X ⋙
        moduleGlobalSectionsDerived.{z} (flatFppfRingedSite X) :=
  (moduleGlobalSectionsDerived.{z} (ringedSite X)).rightDerivedDesc
    (Functor.totalRightDerivedUnit
      (moduleGlobalSectionsToDerived.{z} (ringedSite X))
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSite.ModuleCat.{z} (ringedSite X)) (up ℤ) ⥤
          RingedSite.Hom.ModuleDerived.{z} (ringedSite X))
      (ModuleQis.{z} (ringedSite X)))
    (ModuleQis.{z} (ringedSite X))
    (flatFppfModuleInverseImageDerived X ⋙
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
    lisseEtaleModuleInverseImageCoeff X ⋙
        ModuleSections.Underlying.sections.{z} (lisseEtaleRingedSite X) x ⟶
      ModuleSections.Underlying.sections.{z} (etaleRingedSiteCoeff X)
        ((lisseEtaleInclusion X).obj x) :=
  whiskerLeft (SheafOfModules.toSheaf (etaleStructureSheaf X))
    (SiteAbelianSectionsDerived.sectionsIso (lisseEtaleInclusion X) x).hom

/-- Underived objectwise additive module-sections comparison along flat-fppf
inverse image, transported from the abelian `sectionsIso`. -/
def flatFppfModuleSectionsComparison (x : flatFppfSite X) :
    flatFppfModuleInverseImageCoeff X ⋙
        ModuleSections.Underlying.sections.{z} (flatFppfRingedSite X) x ⟶
      ModuleSections.Underlying.sections.{z} (ringedSite X)
        ((flatFppfInclusion X).obj x) :=
  whiskerLeft (SheafOfModules.toSheaf (structureSheaf X))
    (SiteAbelianSectionsDerived.sectionsIso (flatFppfInclusion X) x).hom

/-- Homotopy-level exact-first unit for lisse-étale module inverse image
followed by objectwise additive sections. -/
def lisseEtaleModuleDerivedSectionsExactFirstUnit (x : lisseEtaleSite X) :
    Functor.Homotopy.toDerived
        (lisseEtaleModuleInverseImageCoeff X ⋙
          ModuleSections.Underlying.sections.{z} (lisseEtaleRingedSite X) x) ⟶
      (DerivedCategory.Qh :
          HomotopyCategory
              (RingedSite.ModuleCat.{z} (etaleRingedSiteCoeff X)) (up ℤ) ⥤
            RingedSite.Hom.ModuleDerived.{z} (etaleRingedSiteCoeff X)) ⋙
        (lisseEtaleModuleInverseImageDerived X ⋙
          ModuleSections.Underlying.sectionsDerived.{z}
            (lisseEtaleRingedSite X) x) :=
  (isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl
          (lisseEtaleModuleInverseImageCoeff X ⋙
            ModuleSections.Underlying.sections.{z} (lisseEtaleRingedSite X)
              x))
        (up ℤ)).symm
      (DerivedCategory.Qh :
        HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
          DerivedCategory AddCommGrpCat.{z})).hom ≫
    (associator
        ((lisseEtaleModuleInverseImageCoeff X).mapHomotopyCategory (up ℤ))
        ((ModuleSections.Underlying.sections.{z} (lisseEtaleRingedSite X)
            x).mapHomotopyCategory (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z})).hom ≫
    Composition.iteratedUnit
      (lisseEtaleModuleInverseImageExact X).obj.mapDerivedCategoryFactorsh.inv
      (Homotopy.unit
        (ModuleSections.Underlying.sections.{z} (lisseEtaleRingedSite X) x))

/-- Homotopy-level exact-first unit for flat-fppf module inverse image
followed by objectwise additive sections. -/
def flatFppfModuleDerivedSectionsExactFirstUnit (x : flatFppfSite X) :
    Functor.Homotopy.toDerived
        (flatFppfModuleInverseImageCoeff X ⋙
          ModuleSections.Underlying.sections.{z} (flatFppfRingedSite X) x) ⟶
      (DerivedCategory.Qh :
          HomotopyCategory (RingedSite.ModuleCat.{z} (ringedSite X)) (up ℤ) ⥤
            RingedSite.Hom.ModuleDerived.{z} (ringedSite X)) ⋙
        (flatFppfModuleInverseImageDerived X ⋙
          ModuleSections.Underlying.sectionsDerived.{z}
            (flatFppfRingedSite X) x) :=
  (isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl
          (flatFppfModuleInverseImageCoeff X ⋙
            ModuleSections.Underlying.sections.{z} (flatFppfRingedSite X)
              x))
        (up ℤ)).symm
      (DerivedCategory.Qh :
        HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
          DerivedCategory AddCommGrpCat.{z})).hom ≫
    (associator
        ((flatFppfModuleInverseImageCoeff X).mapHomotopyCategory (up ℤ))
        ((ModuleSections.Underlying.sections.{z} (flatFppfRingedSite X)
            x).mapHomotopyCategory (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z})).hom ≫
    Composition.iteratedUnit
      (flatFppfModuleInverseImageExact X).obj.mapDerivedCategoryFactorsh.inv
      (Homotopy.unit
        (ModuleSections.Underlying.sections.{z} (flatFppfRingedSite X) x))

/-- Exact derived lisse-étale module inverse image followed by objectwise
derived additive sections is a right-derived functor of the underived
composite. -/
instance lisseEtaleModuleInverseImageDerived_comp_sections_isRightDerived
    (x : lisseEtaleSite X) :
    (lisseEtaleModuleInverseImageDerived X ⋙
        ModuleSections.Underlying.sectionsDerived.{z}
          (lisseEtaleRingedSite X) x).IsRightDerivedFunctor
      (lisseEtaleModuleDerivedSectionsExactFirstUnit X x)
      (ModuleQis.{z} (etaleRingedSiteCoeff X)) :=
  sorry

/-- Exact derived flat-fppf module inverse image followed by objectwise
derived additive sections is a right-derived functor of the underived
composite. -/
instance flatFppfModuleInverseImageDerived_comp_sections_isRightDerived
    (x : flatFppfSite X) :
    (flatFppfModuleInverseImageDerived X ⋙
        ModuleSections.Underlying.sectionsDerived.{z}
          (flatFppfRingedSite X) x).IsRightDerivedFunctor
      (flatFppfModuleDerivedSectionsExactFirstUnit X x)
      (ModuleQis.{z} (ringedSite X)) :=
  sorry

/-- Canonical derived module comparison
`RΓ(X_lisse,étale/x, g^* -) ⟶ RΓ(x, -)`. -/
def lisseEtaleModuleDerivedSectionsComparison (x : lisseEtaleSite X) :
    lisseEtaleModuleInverseImageDerived X ⋙
        ModuleSections.Underlying.sectionsDerived.{z}
          (lisseEtaleRingedSite X) x ⟶
      ModuleSections.Underlying.sectionsDerived.{z} (etaleRingedSiteCoeff X)
        ((lisseEtaleInclusion X).obj x) :=
  (lisseEtaleModuleInverseImageDerived X ⋙
      ModuleSections.Underlying.sectionsDerived.{z}
        (lisseEtaleRingedSite X) x).rightDerivedDesc
    (lisseEtaleModuleDerivedSectionsExactFirstUnit X x)
    (ModuleQis.{z} (etaleRingedSiteCoeff X))
    (ModuleSections.Underlying.sectionsDerived.{z} (etaleRingedSiteCoeff X)
      ((lisseEtaleInclusion X).obj x))
    (whiskerRight
        (NatTrans.mapHomotopyCategory
          (lisseEtaleModuleSectionsComparison X x) (up ℤ))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{z}) ≫
      Homotopy.unit
        (ModuleSections.Underlying.sections.{z} (etaleRingedSiteCoeff X)
          ((lisseEtaleInclusion X).obj x)))

/-- Canonical derived module comparison
`RΓ(X_flat,fppf/x, g^* -) ⟶ RΓ(x, -)`. -/
def flatFppfModuleDerivedSectionsComparison (x : flatFppfSite X) :
    flatFppfModuleInverseImageDerived X ⋙
        ModuleSections.Underlying.sectionsDerived.{z}
          (flatFppfRingedSite X) x ⟶
      ModuleSections.Underlying.sectionsDerived.{z} (ringedSite X)
        ((flatFppfInclusion X).obj x) :=
  (flatFppfModuleInverseImageDerived X ⋙
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

/-- Lemma 104.4.2 (1): on an algebraic stack `X`,
`RΓ(X_étale, K) = RΓ(X_lisse,étale, g⁻¹ K)` in the unbounded derived
category of abelian groups. -/
@[stacks 0H10]
instance lisseEtaleAbelianDerivedGlobalSectionsComparison.instIsIso :
    IsIso (lisseEtaleAbelianDerivedGlobalSectionsComparison X) := sorry

/-- Lemma 104.4.2 (2): on an algebraic stack `X`,
`RΓ(x, K) = RΓ(X_lisse,étale/x, g⁻¹ K)` for every object `x` of the
lisse-étale site. -/
@[stacks 0H10]
instance lisseEtaleAbelianDerivedSectionsComparison.instIsIso
    (x : lisseEtaleSite X) :
    IsIso (lisseEtaleAbelianDerivedSectionsComparison X x) := sorry

/-- Lemma 104.4.2 (3): on an algebraic stack `X`,
`RΓ(X_fppf, K) = RΓ(X_flat,fppf, g⁻¹ K)` in the unbounded derived category
of abelian groups. -/
@[stacks 0H10]
instance flatFppfAbelianDerivedGlobalSectionsComparison.instIsIso :
    IsIso (flatFppfAbelianDerivedGlobalSectionsComparison X) := sorry

/-- Lemma 104.4.2 (4): on an algebraic stack `X`,
`RΓ(x, K) = RΓ(X_flat,fppf/x, g⁻¹ K)` for every object `x` of the
flat-fppf site. -/
@[stacks 0H10]
instance flatFppfAbelianDerivedSectionsComparison.instIsIso
    (x : flatFppfSite X) :
    IsIso (flatFppfAbelianDerivedSectionsComparison X x) := sorry

/-- Lemma 104.4.2 (5): the lisse-étale global comparison of (1) holds for
modules, using `g⁻¹ = g^*` and Cohomology on Sites Lemma 21.20.7. -/
@[stacks 0H10]
instance lisseEtaleModuleDerivedGlobalSectionsComparison.instIsIso :
    IsIso (lisseEtaleModuleDerivedGlobalSectionsComparison X) := sorry

/-- Lemma 104.4.2 (6): the lisse-étale objectwise comparison of (2) holds for
modules, using `g⁻¹ = g^*` and Cohomology on Sites Lemma 21.20.7. -/
@[stacks 0H10]
instance lisseEtaleModuleDerivedSectionsComparison.instIsIso
    (x : lisseEtaleSite X) :
    IsIso (lisseEtaleModuleDerivedSectionsComparison X x) := sorry

/-- Lemma 104.4.2 (7): the flat-fppf global comparison of (3) holds for
modules, using `g⁻¹ = g^*` and Cohomology on Sites Lemma 21.20.7. -/
@[stacks 0H10]
instance flatFppfModuleDerivedGlobalSectionsComparison.instIsIso :
    IsIso (flatFppfModuleDerivedGlobalSectionsComparison X) := sorry

/-- Lemma 104.4.2 (8): the flat-fppf objectwise comparison of (4) holds for
modules, using `g⁻¹ = g^*` and Cohomology on Sites Lemma 21.20.7. -/
@[stacks 0H10]
instance flatFppfModuleDerivedSectionsComparison.instIsIso
    (x : flatFppfSite X) :
    IsIso (flatFppfModuleDerivedSectionsComparison X x) := sorry

end AlgebraicGeometry.AlgebraicStack
