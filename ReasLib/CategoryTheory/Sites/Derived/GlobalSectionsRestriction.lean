/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.Sites.Derived.InverseImage
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.GlobalSections.Naturality
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-! # Restriction of derived global sections along a functor of sites -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD w

namespace CategoryTheory.Sheaf

private instance opensLocallySmall (Y : Type uC) [TopologicalSpace Y] :
    LocallySmall.{uC + 1} (TopologicalSpace.Opens Y) :=
  ⟨fun U V => @Small.trans_univLE.{uC, uC + 1, uC} (U ⟶ V) inferInstance inferInstance⟩

private instance opensSmallModelLimits (Y : Type uC) [TopologicalSpace Y]
    (V : (TopologicalSpace.Opens Y)ᵒᵖ) :
    HasLimitsOfShape
      (StructuredArrow V (equivSmallModel.{uC + 1} (TopologicalSpace.Opens Y)).inverse.op)
      AddCommGrpCat.{uC + 1} :=
  HasLimitsOfShape.of_small _ _

private theorem opensGrothendieckProof (Y : Type uC) [TopologicalSpace Y]
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{uC + 1}] :
    IsGrothendieckAbelian.{uC + 1}
      (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{uC + 1}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{uC + 1}
    (Opens.grothendieckTopology Y) AddCommGrpCat.{uC + 1}

set_option backward.privateInPublic true in
/-- Abelian sheaves on the open-set site of a topological space form a
Grothendieck abelian category when coefficients lie in the next universe. -/
instance opensGrothendieckLargerCoefficients (Y : Type uC) [TopologicalSpace Y]
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{uC + 1}] :
    IsGrothendieckAbelian.{uC + 1}
      (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{uC + 1}) :=
  opensGrothendieckProof Y

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable (f : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [f.IsContinuous J K] [f.IsCocontinuous J K]
variable [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor K AddCommGrpCat.{w}]
variable [HasLimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
variable [HasLimitsOfShape Dᵒᵖ AddCommGrpCat.{w}]
variable [IsGrothendieckAbelian (Sheaf J AddCommGrpCat.{w})]
variable [IsGrothendieckAbelian (Sheaf K AddCommGrpCat.{w})]

/-- The cochain-level restriction comparison followed by the canonical derived
global-sections unit and the exact inverse-image localization isomorphism. -/
def derivedGlobalSectionsRestrictionUnit :
    Functor.RightDerived.Cochain.toDerived (Γ K AddCommGrpCat.{w}) ⟶
      DerivedCategory.Q ⋙ siteAbelianInverseImageDerived J K f ⋙
        siteAbelianGlobalSectionsDerived J :=
  Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (globalSectionsPushforwardNat f J K)
        (ComplexShape.up ℤ)) DerivedCategory.Q ≫
    (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (f.sheafPushforwardContinuous AddCommGrpCat.{w} J K ⋙
          Γ J AddCommGrpCat.{w})) (ComplexShape.up ℤ)).symm
      DerivedCategory.Q).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      ((siteAbelianInverseImageExact J K f).obj.mapHomologicalComplex (ComplexShape.up ℤ))
      (Functor.RightDerived.Cochain.unit (Γ J AddCommGrpCat.{w})) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (siteAbelianInverseImageExact J K f).obj.mapDerivedCategoryFactors.inv
      (siteAbelianGlobalSectionsDerived J) ≫
    (Functor.associator _ _ _).hom

/-- Canonical restriction of derived global sections to the inverse image along
a continuous and cocontinuous functor of sites. -/
def derivedGlobalSectionsRestriction :
    siteAbelianGlobalSectionsDerived K ⟶
      siteAbelianInverseImageDerived J K f ⋙ siteAbelianGlobalSectionsDerived J :=
  (siteAbelianGlobalSectionsDerived K).rightDerivedDesc
    (Functor.RightDerived.Cochain.unit (Γ K AddCommGrpCat.{w}))
    (HomologicalComplex.quasiIso (Sheaf K AddCommGrpCat.{w}) (ComplexShape.up ℤ))
    (siteAbelianInverseImageDerived J K f ⋙ siteAbelianGlobalSectionsDerived J)
    (derivedGlobalSectionsRestrictionUnit f J K)

/-- Restriction of derived global sections factors the underived restriction
through the canonical right-derived comparison units. -/
theorem derivedGlobalSectionsRestriction_fac :
    Functor.RightDerived.Cochain.unit (Γ K AddCommGrpCat.{w}) ≫
      Functor.whiskerLeft DerivedCategory.Q (derivedGlobalSectionsRestriction f J K) =
        derivedGlobalSectionsRestrictionUnit f J K := by
  apply Functor.rightDerived_fac

end CategoryTheory.Sheaf
