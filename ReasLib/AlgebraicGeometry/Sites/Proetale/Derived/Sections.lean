/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Definition
public import ReasLib.CategoryTheory.Sites.Derived.Sections

/-!
# Bounded-Below Derived Global Pro-étale Sections

Derived global sections on the small pro-étale site of a quasi-compact quasi-separated
scheme preserve existing bounded-below coproducts and sequential homotopy colimits.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

/-- Bounded-below derived global sections `RΓ(X, -)` on abelian sheaves on the small
pro-étale site, valued in `D(Ab)`. -/
abbrev globalSectionsPlusDerived (X : Scheme.{u})
    [HasSheafify (topology X) AddCommGrpCat.{u}]
    [Functor.HasRightDerivedFunctor
      ((siteAbelianSectionsFunctor (topology X) (ProEt.mk (𝟙 X))).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology X) AddCommGrpCat.{u}))] :
    DerivedCategory.Plus (Sheaf (topology X) AddCommGrpCat.{u}) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  siteAbelianSectionsBoundedBelowDerived (topology X) (ProEt.mk (𝟙 X)) ⋙
    DerivedCategory.Plus.ι

/-- Derived global sections on the small pro-étale site of a quasi-compact
quasi-separated scheme preserve every coproduct that exists in the bounded-below
derived category of abelian sheaves. -/
instance rGamma_preservesCoproduct {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasSheafify (topology X) AddCommGrpCat.{u}]
    [Functor.HasRightDerivedFunctor
      ((siteAbelianSectionsFunctor (topology X) (ProEt.mk (𝟙 X))).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology X) AddCommGrpCat.{u}))]
    {I : Type w} (E : I → DerivedCategory.Plus (Sheaf (topology X) AddCommGrpCat.{u}))
    [HasCoproduct E] :
    PreservesColimit (Discrete.functor E) (globalSectionsPlusDerived X) := sorry

/-- Derived global sections on the small pro-étale site of a quasi-compact
quasi-separated scheme preserve existing sequential homotopy colimits in the
bounded-below derived category of abelian sheaves. -/
theorem rGamma_preservesHomotopyColimit {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasSheafify (topology X) AddCommGrpCat.{u}]
    [Functor.HasRightDerivedFunctor
      ((siteAbelianSectionsFunctor (topology X) (ProEt.mk (𝟙 X))).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology X) AddCommGrpCat.{u}))]
    (K : ℕ ⥤ DerivedCategory.Plus (Sheaf (topology X) AddCommGrpCat.{u}))
    {E : DerivedCategory.Plus (Sheaf (topology X) AddCommGrpCat.{u})}
    (h : HomotopyColimit.IsOf K E) :
    HomotopyColimit.IsOf (K ⋙ globalSectionsPlusDerived X)
      ((globalSectionsPlusDerived X).obj E) := sorry

end AlgebraicGeometry.Scheme.ProEt

end
