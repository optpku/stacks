/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Definition
public import ReasLib.CategoryTheory.Sites.Derived.Sections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.14.3

On a quasi-compact quasi-separated scheme, derived global sections on the small
pro-étale site commute with those direct sums that exist in `D⁺` and with sequential
homotopy colimits.
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

/-- Unfolding of bounded-below derived global pro-étale sections as site-derived sections
at `ProEt.mk (𝟙 X)` followed by `DerivedCategory.Plus.ι`. -/
theorem globalSectionsPlusDerived_eq (X : Scheme.{u})
    [HasSheafify (topology X) AddCommGrpCat.{u}]
    [Functor.HasRightDerivedFunctor
      ((siteAbelianSectionsFunctor (topology X) (ProEt.mk (𝟙 X))).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology X) AddCommGrpCat.{u}))] :
    globalSectionsPlusDerived X =
      siteAbelianSectionsBoundedBelowDerived (topology X) (ProEt.mk (𝟙 X)) ⋙
        DerivedCategory.Plus.ι := sorry

/-- Lemma 61.14.3 (1): if `X` is quasi-compact and quasi-separated and `E` is a family in
`D⁺(X.ProEt)` whose coproduct still lies in `D⁺`, then `RΓ(X, -)` preserves that coproduct. -/
@[stacks 09A3]
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

/-- Canonical identification `RΓ(X, ∐ E) ≅ ∐ fun i ↦ RΓ(X, E i)` in `D(Ab)`. -/
def rGamma_coproductIso {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasSheafify (topology X) AddCommGrpCat.{u}]
    [Functor.HasRightDerivedFunctor
      ((siteAbelianSectionsFunctor (topology X) (ProEt.mk (𝟙 X))).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology X) AddCommGrpCat.{u}))]
    {I : Type w} (E : I → DerivedCategory.Plus (Sheaf (topology X) AddCommGrpCat.{u}))
    [HasCoproduct E]
    [HasCoproduct (fun i ↦ (globalSectionsPlusDerived X).obj (E i))] :
    (globalSectionsPlusDerived X).obj (∐ E) ≅
      ∐ fun i ↦ (globalSectionsPlusDerived X).obj (E i) :=
  PreservesCoproduct.iso (globalSectionsPlusDerived X) E

/-- Lemma 61.14.3 (2): if `X` is quasi-compact and quasi-separated, then `RΓ(X, -)`
preserves sequential homotopy colimits that exist in `D⁺(X.ProEt)`. -/
@[stacks 09A3]
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
