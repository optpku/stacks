/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.CategoryTheory.Sites.GlobalSections.Hom
public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive

/-! # Sheaf cohomology and right-derived global sections -/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open HomologicalComplex Opposite ComplexShape CochainComplex.HomComplex

noncomputable section

universe u v

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor J AddCommGrpCat.{max u v}]

/-- Morphisms from the constant integer sheaf are naturally global sections when
coefficients contain both universes of the site. -/
def globalSectionsHomIsoSameUniverse :
    globalSectionsHomFunctor J ≅ Γ J AddCommGrpCat.{max u v} :=
  NatIso.ofComponents
    (fun F ↦ (globalSectionsAddEquivConstantIntegerSheafHomOnSite J F).toAddCommGrpIso.symm)
    sorry

variable [HasExt.{max u v} (Sheaf J AddCommGrpCat.{max u v})]

/-- Homology of the constant-integer Hom complex of an injective resolution
computes Ext from the constant integer sheaf. -/
def homologyGlobalSectionsHomExtIso
    {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F) (i : ℕ) :
    (((globalSectionsHomFunctor J).mapHomologicalComplex (up ℤ)).obj
        I.cochainComplex).homology (Int.ofNat i) ≅
      AddCommGrpCat.of (Ext (constantIntegerSheaf J) F i) :=
  let Z : Sheaf J AddCommGrpCat.{max u v} := constantIntegerSheaf J
  let K := (CochainComplex.singleFunctor _ 0).obj Z
  let E := AddCommGrpCat.of (CohomologyClass K I.cochainComplex (Int.ofNat i))
  HomologicalComplex.homologyMapIso
      (HomologicalComplex.Hom.isoOfComponents
        (fun n ↦
          (Cochain.fromSingleEquiv (zero_add n) :
            Cochain K I.cochainComplex n ≃+ (Z ⟶ I.cochainComplex.X n)).symm.toAddCommGrpIso)
        sorry)
      (Int.ofNat i) ≪≫
    (homologyAddEquiv K I.cochainComplex (Int.ofNat i)).toAddCommGrpIso (Y := E) ≪≫
    (I.extAddEquivCohomologyClass : Ext Z F i ≃+
      CohomologyClass K I.cochainComplex i).symm.toAddCommGrpIso (X := E)

variable [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})]

/-- Sheaf cohomology is computed by right-derived global sections. -/
def functorHIsoGammaRightDerived (i : ℕ) (F : Sheaf J AddCommGrpCat.{max u v}) :
    (functorH J i).obj F ≅ ((Γ J AddCommGrpCat.{max u v}).rightDerived i).obj F :=
  (Iso.refl ((functorH J i).obj F) :
    (functorH J i).obj F ≅ AddCommGrpCat.of (Ext (constantIntegerSheaf J) F i)) ≪≫
    (homologyGlobalSectionsHomExtIso J (injectiveResolution F) i).symm ≪≫
    InjectiveResolution.RightDerived.homologyIso (injectiveResolution F)
      (globalSectionsHomFunctor J) i ≪≫
    (CategoryTheory.NatIso.rightDerived (globalSectionsHomIsoSameUniverse J) i).app F

end CategoryTheory.Sheaf
