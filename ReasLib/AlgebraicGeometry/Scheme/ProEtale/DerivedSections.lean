/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.CategoryTheory.Sites.Derived.Sections

/-!
# Global sections on the small pro-étale site

The identity object of `X.ProEt` and the derived global sections functor
`RΓ(X, -)` on abelian sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- The identity object of the small pro-étale site of a scheme. -/
abbrev globalProEt (X : Scheme.{u}) : X.ProEt :=
  ProEt.mk (𝟙 X)

/-- The structure morphism of the identity pro-étale object is the identity. -/
theorem globalProEt_hom (X : Scheme.{u}) : (globalProEt X).hom = 𝟙 X := sorry

/-- The identity object of the small pro-étale site is terminal. -/
def globalProEt_isTerminal (X : Scheme.{u}) : IsTerminal (globalProEt X) :=
  MorphismProperty.Over.mkIdTerminal @WeaklyEtale X

/-- Derived global sections `RΓ(X, -)` on abelian sheaves on the small pro-étale site. -/
abbrev globalSectionsDerived (X : Scheme.{u})
    [HasSheafify (topology X) AddCommGrpCat.{u}]
    [IsGrothendieckAbelian (Sheaf (topology X) AddCommGrpCat.{u})]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (siteAbelianSectionsFunctor (topology X) (globalProEt X)))
      (HomologicalComplex.quasiIso (Sheaf (topology X) AddCommGrpCat.{u}) (up ℤ))] :
    DerivedCategory (Sheaf (topology X) AddCommGrpCat.{u}) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  siteAbelianSectionsDerived (topology X) (globalProEt X)

/-- Derived global pro-étale sections agree with site-derived sections at `globalProEt X`. -/
theorem globalSectionsDerived_eq (X : Scheme.{u})
    [HasSheafify (topology X) AddCommGrpCat.{u}]
    [IsGrothendieckAbelian (Sheaf (topology X) AddCommGrpCat.{u})]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (siteAbelianSectionsFunctor (topology X) (globalProEt X)))
      (HomologicalComplex.quasiIso (Sheaf (topology X) AddCommGrpCat.{u}) (up ℤ))] :
    globalSectionsDerived X =
      siteAbelianSectionsDerived (topology X) (globalProEt X) := sorry

end AlgebraicGeometry.Scheme.ProEt
