/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Universe
public import ReasLib.CategoryTheory.Sites.GlobalSections.Universe
public import ReasLib.CategoryTheory.Sites.GlobalSections.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.Sites.Derived.SectionsComparison
public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedConstantInteger
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedLowerShriek
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

/-- Cochain-level unit of the underived lisse-étale global comparison, composed
with the exact-first unit of derived inverse image. -/
def lisseEtaleAbelianDerivedGlobalSectionsUnit :
    Cochain.toDerived (Sheaf.Γ X.etaleTopology AddCommGrpCat.{z}) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{z}) ℤ ⥤
            DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{z})) ⋙
        ((siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
          (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X)) ⋙
          Cochain.functor (Sheaf.Γ (lisseEtaleTopology X) AddCommGrpCat.{z})) :=
  whiskerRight
      (NatTrans.mapHomologicalComplex
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
            exact HasLimitsOfShape.of_small _ _)) (up ℤ))
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
        ((siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
          (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X)) ⋙
          Cochain.functor (Sheaf.Γ (flatFppfTopology X) AddCommGrpCat.{z})) :=
  whiskerRight
      (NatTrans.mapHomologicalComplex
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
            exact HasLimitsOfShape.of_small _ _)) (up ℤ))
      (DerivedCategory.Q :
        CochainComplex AddCommGrpCat.{z} ℤ ⥤ DerivedCategory AddCommGrpCat.{z}) ≫
    Cochain.ExactFirst.unit
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
        (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X))
      (Sheaf.Γ (flatFppfTopology X) AddCommGrpCat.{z})

/-- The canonical comparison from derived étale global sections to derived lisse-étale global
sections after inverse image. -/
def lisseEtaleAbelianDerivedGlobalSectionsComparison :
    Cochain.functor (Sheaf.Γ X.etaleTopology AddCommGrpCat.{z}) ⟶
      (siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
        (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X)) ⋙
        Cochain.functor (Sheaf.Γ (lisseEtaleTopology X) AddCommGrpCat.{z}) :=
  (Cochain.functor (Sheaf.Γ X.etaleTopology AddCommGrpCat.{z})).rightDerivedDesc
    (Cochain.unit (Sheaf.Γ X.etaleTopology AddCommGrpCat.{z}))
    (HomologicalComplex.quasiIso
      (Sheaf X.etaleTopology AddCommGrpCat.{z}) (up ℤ))
    ((siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X)) ⋙
      Cochain.functor (Sheaf.Γ (lisseEtaleTopology X) AddCommGrpCat.{z}))
    (lisseEtaleAbelianDerivedGlobalSectionsUnit X)

/-- The canonical comparison from derived fppf global sections to derived flat-fppf global
sections after inverse image. -/
def flatFppfAbelianDerivedGlobalSectionsComparison :
    Cochain.functor (Sheaf.Γ (inheritedFppfTopology X) AddCommGrpCat.{z}) ⟶
      (siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
        (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X)) ⋙
        Cochain.functor (Sheaf.Γ (flatFppfTopology X) AddCommGrpCat.{z}) :=
  (Cochain.functor
      (Sheaf.Γ (inheritedFppfTopology X) AddCommGrpCat.{z})).rightDerivedDesc
    (Cochain.unit (Sheaf.Γ (inheritedFppfTopology X) AddCommGrpCat.{z}))
    (HomologicalComplex.quasiIso
      (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) (up ℤ))
    ((siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X)) ⋙
      Cochain.functor (Sheaf.Γ (flatFppfTopology X) AddCommGrpCat.{z}))
    (flatFppfAbelianDerivedGlobalSectionsUnit X)

/-- Exact derived lisse-étale inverse image followed by objectwise derived
sections is a right-derived functor of the underived composite. -/
instance lisseEtaleAbelianInverseImageDerived_comp_sections_isRightDerived
    (x : lisseEtaleSite X) :
    ((siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X)) ⋙
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
    ((siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X)) ⋙
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
    (siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X)) ⋙
        siteAbelianSectionsDerived (lisseEtaleTopology X) x ⟶
      siteAbelianSectionsDerived X.etaleTopology
        ((lisseEtaleInclusion X).obj x) :=
  rightDerivedNatTrans
    ((siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X)) ⋙
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
    (siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X)) ⋙
        siteAbelianSectionsDerived (flatFppfTopology X) x ⟶
      siteAbelianSectionsDerived (inheritedFppfTopology X)
        ((flatFppfInclusion X).obj x) :=
  rightDerivedNatTrans
    ((siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X)) ⋙
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

/-- The canonical lisse-étale derived global sections comparison for abelian coefficients is
invertible. -/
@[stacks 0H10]
instance lisseEtaleAbelianDerivedGlobalSectionsComparison.instIsIso :
    IsIso (lisseEtaleAbelianDerivedGlobalSectionsComparison X) := sorry

/-- The canonical lisse-étale derived objectwise sections comparison for abelian coefficients is
invertible. -/
@[stacks 0H10]
instance lisseEtaleAbelianDerivedSectionsComparison.instIsIso
    (x : lisseEtaleSite X) :
    IsIso (lisseEtaleAbelianDerivedSectionsComparison X x) := sorry

/-- The canonical flat-fppf derived global sections comparison for abelian coefficients is
invertible. -/
@[stacks 0H10]
instance flatFppfAbelianDerivedGlobalSectionsComparison.instIsIso :
    IsIso (flatFppfAbelianDerivedGlobalSectionsComparison X) := sorry

/-- The canonical flat-fppf derived objectwise sections comparison for abelian coefficients is
invertible. -/
@[stacks 0H10]
instance flatFppfAbelianDerivedSectionsComparison.instIsIso
    (x : flatFppfSite X) :
    IsIso (flatFppfAbelianDerivedSectionsComparison X x) := sorry

/-- The derived comparison factors its defining localization unit. -/
lemma lisseEtaleAbelianDerivedGlobalSectionsComparison_fac :
    (Cochain.unit (Sheaf.Γ X.etaleTopology AddCommGrpCat.{z})) ≫
      whiskerLeft (DerivedCategory.Q : CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{z}) ℤ ⥤ _)
        (lisseEtaleAbelianDerivedGlobalSectionsComparison X) =
    (lisseEtaleAbelianDerivedGlobalSectionsUnit X) := by
  exact (Cochain.functor (Sheaf.Γ X.etaleTopology AddCommGrpCat.{z})).rightDerived_fac
    (Cochain.unit (Sheaf.Γ X.etaleTopology AddCommGrpCat.{z}))
    (HomologicalComplex.quasiIso
      (Sheaf X.etaleTopology AddCommGrpCat.{z}) (up ℤ))
    ((siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X)) ⋙
      Cochain.functor (Sheaf.Γ (lisseEtaleTopology X) AddCommGrpCat.{z}))
    (lisseEtaleAbelianDerivedGlobalSectionsUnit X)

/-- The derived comparison factors its defining localization unit. -/
lemma flatFppfAbelianDerivedGlobalSectionsComparison_fac :
    (Cochain.unit (Sheaf.Γ (inheritedFppfTopology X) AddCommGrpCat.{z})) ≫
      whiskerLeft (DerivedCategory.Q : CochainComplex (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) ℤ ⥤ _)
        (flatFppfAbelianDerivedGlobalSectionsComparison X) =
    (flatFppfAbelianDerivedGlobalSectionsUnit X) := by
  exact (Cochain.functor
      (Sheaf.Γ (inheritedFppfTopology X) AddCommGrpCat.{z})).rightDerived_fac
    (Cochain.unit (Sheaf.Γ (inheritedFppfTopology X) AddCommGrpCat.{z}))
    (HomologicalComplex.quasiIso
      (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) (up ℤ))
    ((siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X)) ⋙
      Cochain.functor (Sheaf.Γ (flatFppfTopology X) AddCommGrpCat.{z}))
    (flatFppfAbelianDerivedGlobalSectionsUnit X)

/-- The derived comparison factors its defining localization unit. -/
lemma lisseEtaleAbelianDerivedSectionsComparison_fac (x : lisseEtaleSite X) :
    (Cochain.ExactFirst.unit
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
        (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X))
      (siteAbelianSectionsFunctor (lisseEtaleTopology X) x)) ≫
      whiskerLeft (DerivedCategory.Q : CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{z}) ℤ ⥤ _)
        (lisseEtaleAbelianDerivedSectionsComparison X x) =
    (SiteAbelianSectionsDerived.sectionsToDerivedIso
      (lisseEtaleInclusion X) x).hom ≫ ((Cochain.toDerived
        (siteAbelianSectionsFunctor X.etaleTopology
          ((lisseEtaleInclusion X).obj x))).totalRightDerivedUnit
      (DerivedCategory.Q :
        CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{z}) ℤ ⥤
          DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{z}))
      (HomologicalComplex.quasiIso
        (Sheaf X.etaleTopology AddCommGrpCat.{z}) (up ℤ))) := by
  exact Functor.rightDerivedNatTrans_fac
    ((siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X)) ⋙
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

/-- The derived comparison factors its defining localization unit. -/
lemma flatFppfAbelianDerivedSectionsComparison_fac (x : flatFppfSite X) :
    (Cochain.ExactFirst.unit
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
        (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X))
      (siteAbelianSectionsFunctor (flatFppfTopology X) x)) ≫
      whiskerLeft (DerivedCategory.Q : CochainComplex (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) ℤ ⥤ _)
        (flatFppfAbelianDerivedSectionsComparison X x) =
    (SiteAbelianSectionsDerived.sectionsToDerivedIso
      (flatFppfInclusion X) x).hom ≫ ((Cochain.toDerived
        (siteAbelianSectionsFunctor (inheritedFppfTopology X)
          ((flatFppfInclusion X).obj x))).totalRightDerivedUnit
      (DerivedCategory.Q :
        CochainComplex
            (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) ℤ ⥤
          DerivedCategory
            (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}))
      (HomologicalComplex.quasiIso
        (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) (up ℤ))) := by
  exact Functor.rightDerivedNatTrans_fac
    ((siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X)) ⋙
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

end AlgebraicGeometry.AlgebraicStack
