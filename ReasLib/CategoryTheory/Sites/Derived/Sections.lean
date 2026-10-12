/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Sites.AbelianSheaf
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived

/-!
# Derived Sections of Abelian Sheaves

This module provides sections on a site of abelian sheaves, its bounded and unbounded right
derived functors, and the injective-resolution computation of the derived inclusion into
presheaves.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]

/-- The sections functor `Γ(U, -)` on abelian sheaves over a site. -/
@[stacks 0DD8 "abelian sections functor"]
abbrev siteAbelianSectionsFunctor (J : GrothendieckTopology C) (U : C)
    [HasSheafify J AddCommGrpCat.{w}] :
    Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
  (sheafSections J AddCommGrpCat.{w}).obj (op U)

/-- The sections functor on abelian sheaves is additive. -/
instance siteAbelianSectionsFunctor_additive (J : GrothendieckTopology C) (U : C)
    [HasSheafify J AddCommGrpCat.{w}] :
    (siteAbelianSectionsFunctor J U).Additive := by
  -- Pin the evaluation presentation used by `sheafSectionsNatIsoEvaluation`.
  let F : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
    sheafToPresheaf J AddCommGrpCat.{w} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U)
  -- Local instance justification (defeq pin): pin the transported additive structure on the
  -- evaluation presentation used by `sheafSectionsNatIsoEvaluation`.
  letI : F.Additive := inferInstance
  simpa [F, siteAbelianSectionsFunctor] using
    (Functor.additive_of_iso
      (sheafSectionsNatIsoEvaluation (J := J) (A := AddCommGrpCat.{w}) (X := U)).symm)

/-- The sections functor on abelian sheaves preserves finite limits. -/
instance siteAbelianSectionsFunctor_preservesFiniteLimits
    (J : GrothendieckTopology C) (U : C)
    [HasSheafify J AddCommGrpCat.{w}] :
    PreservesFiniteLimits (siteAbelianSectionsFunctor J U) := by
  -- Pin the same evaluation presentation before transporting finite limits across the isomorphism.
  let F : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
    sheafToPresheaf J AddCommGrpCat.{w} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U)
  -- Local instance justification (defeq pin): pin the transported finite-limit structure on the
  -- evaluation presentation before applying `preservesFiniteLimits_of_natIso`.
  letI : PreservesFiniteLimits F := inferInstance
  simpa [F, siteAbelianSectionsFunctor] using
    (preservesFiniteLimits_of_natIso
      (sheafSectionsNatIsoEvaluation (J := J) (A := AddCommGrpCat.{w}) (X := U)).symm)

namespace Sheaf

/-- Evaluating the degree-`p` right derived functor of the inclusion
`sheafToPresheaf J AddCommGrpCat` at `U` identifies it with the degree-`p` homology of the
sections complex `Γ(U, I^•)` of an injective resolution `I` of `F`. -/
noncomputable def rightDerivedInclusion_app_obj_iso_homology_sections_complex
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasExt.{max u v} (Sheaf J AddCommGrpCat.{max u v})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})]
    {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F) (U : C) (p : ℕ) :
    ((((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p).obj F).obj (op U)) ≅
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℕ) p).obj
        (((siteAbelianSectionsFunctor J U).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)) := by
  let K :
      HomologicalComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (ComplexShape.up ℕ) :=
    (((sheafToPresheaf J AddCommGrpCat.{max u v}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex)
  let evalU := (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)
  let eDerived :
      ((((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p).obj F).obj (op U)) ≅
        (evalU.obj
          ((HomologicalComplex.homologyFunctor
            (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (ComplexShape.up ℕ) p).obj K)) :=
    evalU.mapIso (I.isoRightDerivedObj (sheafToPresheaf J AddCommGrpCat.{max u v}) p)
  let eHomology :
      (evalU.obj
          ((HomologicalComplex.homologyFunctor
            (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (ComplexShape.up ℕ) p).obj K)) ≅
        ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℕ) p).obj
          ((evalU.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)) := by
    exact
      (evalU.mapIso
        ((HomologicalComplex.homologyFunctorIso
          (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (ComplexShape.up ℕ) p).app K)) ≪≫
        ((K.sc p).mapHomologyIso evalU).symm ≪≫
          ((HomologicalComplex.homologyFunctorIso
            AddCommGrpCat.{max u v} (ComplexShape.up ℕ) p).app
            ((evalU.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)).symm
  let eComp :
      (sheafToPresheaf J AddCommGrpCat.{max u v}).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        evalU.mapHomologicalComplex (ComplexShape.up ℕ) ≅
      (sheafToPresheaf J AddCommGrpCat.{max u v} ⋙ evalU).mapHomologicalComplex
        (ComplexShape.up ℕ) :=
    Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℕ)
  let eSections :
      ((evalU.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ≅
        ((siteAbelianSectionsFunctor J U).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex :=
    eComp.app I.cocomplex ≪≫
      ((NatIso.mapHomologicalComplex
        (sheafSectionsNatIsoEvaluation
          (J := J) (A := AddCommGrpCat.{max u v}) (X := U))
        (ComplexShape.up ℕ)).app I.cocomplex).symm
  let eHomologySections :=
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℕ) p).mapIso
      eSections
  simpa [K, evalU, siteAbelianSectionsFunctor, sheafSections] using
    (eDerived.trans eHomology).trans eHomologySections

end Sheaf

/-- The chosen unbounded derived sections functor `RΓ(U, -)` on abelian sheaves over a site. -/
@[stacks 0DD8 "derived abelian sections"]
abbrev siteAbelianSectionsDerived (J : GrothendieckTopology C) (U : C)
    [HasSheafify J AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf J AddCommGrpCat.{w})] :
    DerivedCategory (Sheaf J AddCommGrpCat.{w}) ⥤
      DerivedCategory AddCommGrpCat.{w} :=
  Functor.RightDerived.Cochain.functor (siteAbelianSectionsFunctor J U)

/-- The bounded-below derived sections functor `RΓ(U, -)` on abelian sheaves over a site,
valued in `D⁺(AddCommGrpCat)`. -/
@[stacks 0DD8 "bounded-below derived abelian sections"]
abbrev siteAbelianSectionsBoundedBelowDerived (J : GrothendieckTopology C) (U : C)
    [HasSheafify J AddCommGrpCat.{w}]
    [Functor.HasRightDerivedFunctor
      ((siteAbelianSectionsFunctor J U).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{w}))] :
    DerivedCategory.Plus (Sheaf J AddCommGrpCat.{w}) ⥤
      DerivedCategory.Plus AddCommGrpCat.{w} :=
  Functor.totalRightDerived
    ((siteAbelianSectionsFunctor J U).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
    DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{w}))

/-- The bounded-below derived-sections target `F ↦ RΓ(U, F[0])` on abelian sheaves. -/
abbrev sheafToBoundedBelowDerivedSectionsFunctor (J : GrothendieckTopology C) (U : C)
    [HasSheafify J AddCommGrpCat.{w}]
    [Functor.HasRightDerivedFunctor
      ((siteAbelianSectionsFunctor J U).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{w}))] :
    Sheaf J AddCommGrpCat.{w} ⥤ DerivedCategory.Plus AddCommGrpCat.{w} :=
  DerivedCategory.Plus.singleFunctor (Sheaf J AddCommGrpCat.{w}) 0 ⋙
    siteAbelianSectionsBoundedBelowDerived J U

namespace SiteAbelianSectionsDerived

@[inherit_doc CategoryTheory.siteAbelianSectionsDerived]
scoped[GrothendieckTopologyDerivedSections] notation3:max "RΓ[" J "](" U ")" =>
  CategoryTheory.siteAbelianSectionsDerived J U

end SiteAbelianSectionsDerived

end

end CategoryTheory
