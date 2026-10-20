/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.YonedaPushforward
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Functor Limits Opposite FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u w

/-! The source identification is owned by the reusable Yoneda pushforward API. -/

/- 96.5.0.1 -/
@[stacks 06W6] #check
  (CategoryTheory.FiberedCategoryOver.Groupoids.pushforwardObjIsoGlobalSections :
    {S : Scheme.{u}} →
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)} →
    (f : X ⟶ Y) →
    [∀ P : Presheaf X.total, (toFunctor f).op.HasRightKanExtension P] →
    {V : Over S} →
    (y : Y.p.Fiber V) →
    (F : Presheaf X.total) →
    [(toFunctor f).op.HasPointwiseRightKanExtension F] →
    [HasLimit ((toFunctor (CategoryTheory.FiberedCategoryOver.Groupoids.yonedaFibreProduct.pr f y)).op ⋙ F)] →
    ((toFunctor f).op.ran.obj F).obj (op y.1) ≅
      limit ((toFunctor (CategoryTheory.FiberedCategoryOver.Groupoids.yonedaFibreProduct.pr f y)).op ⋙ F))
