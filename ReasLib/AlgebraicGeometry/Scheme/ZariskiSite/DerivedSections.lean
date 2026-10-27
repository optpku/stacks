/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Pushforward
public import ReasLib.CategoryTheory.Sites.Derived.SectionsComparison

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v dX dX'

namespace AlgebraicGeometry.Scheme

/-- Global sections of a Zariski direct image are naturally the global sections on the source
scheme. -/
def zariskiAbelianSectionsPushforwardIso {X' X : Scheme.{u}} (f : X' ⟶ X)
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{v}]
    [HasSheafify X'.smallZariskiTopology AddCommGrpCat.{v}] :
    zariskiAbelianPushforward.{u, v} f ⋙
        siteAbelianSectionsFunctor X.smallZariskiTopology
          ((smallZariskiOpenFunctor X).obj ⊤) ≅
      siteAbelianSectionsFunctor X'.smallZariskiTopology
        ((smallZariskiOpenFunctor X').obj ⊤) :=
  SiteAbelianSectionsDerived.sectionsIso (smallZariskiPullback f)
      ((smallZariskiOpenFunctor X).obj ⊤) ≪≫
    (sheafSections X'.smallZariskiTopology AddCommGrpCat.{v}).mapIso
      ((smallZariskiPullbackOpenFunctorIso f).app ⊤).symm.op

/-- Zariski direct image along a homeomorphism preserves injective abelian sheaves. -/
instance zariskiAbelianPushforwardExact_preservesInjectiveObjects
    {X' X : Scheme.{u}} (f : X' ⟶ X) (hf : IsHomeomorph f) :
    (zariskiAbelianPushforwardExact.{u, v} f hf).obj.PreservesInjectiveObjects := sorry

/-- Derived global sections commute with Zariski direct image along a homeomorphism, for
independently chosen derived-category models of the two categories of sheaves. -/
def zariskiAbelianDerivedSectionsPushforwardIso {X' X : Scheme.{u}} (f : X' ⟶ X)
    (hf : IsHomeomorph f)
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{v}]
    [HasSheafify X'.smallZariskiTopology AddCommGrpCat.{v}]
    [HasDerivedCategory.{dX} (Sheaf X.smallZariskiTopology AddCommGrpCat.{v})]
    [HasDerivedCategory.{dX'} (Sheaf X'.smallZariskiTopology AddCommGrpCat.{v})]
    [IsGrothendieckAbelian (Sheaf X.smallZariskiTopology AddCommGrpCat.{v})]
    [IsGrothendieckAbelian (Sheaf X'.smallZariskiTopology AddCommGrpCat.{v})] :
    (zariskiAbelianPushforwardExact.{u, v} f hf).mapDerivedCategory ⋙
        (siteAbelianSectionsDerivedWith X.smallZariskiTopology
          ((smallZariskiOpenFunctor X).obj ⊤) :
          DerivedCategory.{dX} (Sheaf X.smallZariskiTopology AddCommGrpCat.{v}) ⥤
            DerivedCategory AddCommGrpCat.{v}) ≅
      (siteAbelianSectionsDerivedWith X'.smallZariskiTopology
        ((smallZariskiOpenFunctor X').obj ⊤) :
        DerivedCategory.{dX'} (Sheaf X'.smallZariskiTopology AddCommGrpCat.{v}) ⥤
          DerivedCategory AddCommGrpCat.{v}) :=
  Functor.RightDerived.Cochain.ExactFirst.iso
      (zariskiAbelianPushforwardExact.{u, v} f hf)
      (siteAbelianSectionsFunctor X.smallZariskiTopology
        ((smallZariskiOpenFunctor X).obj ⊤)) ≪≫
    Functor.RightDerived.mapNatIso
      (DerivedCategory.Q : CochainComplex
        (Sheaf X'.smallZariskiTopology AddCommGrpCat.{v}) ℤ ⥤
          DerivedCategory.{dX'} (Sheaf X'.smallZariskiTopology AddCommGrpCat.{v}))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallZariskiTopology AddCommGrpCat.{v}) (ComplexShape.up ℤ))
      (Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex (zariskiAbelianSectionsPushforwardIso.{u, v} f)
          (ComplexShape.up ℤ))
        (DerivedCategory.Q : CochainComplex AddCommGrpCat.{v} ℤ ⥤
          DerivedCategory AddCommGrpCat.{v}))

end AlgebraicGeometry.Scheme
