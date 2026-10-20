/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.InGroupoids.PseudoPullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Slice base changes of groupoid fibrations

The first projection of the explicit pseudo-pullback of a slice morphism and a morphism of
groupoid fibrations, bundled as a groupoid fibration over the slice category.
-/

@[expose] public section

universe u v uX vX uY vY

namespace CategoryTheory

open BasedCategory

variable {C : Type u} [Category.{v} C]

namespace BasedCategory.PseudoPullback

/-- For a morphism `F : X ⥤ᵇ Y` of categories fibred in
groupoids over `C` and a slice morphism `G : C/U ⥤ᵇ Y`, the first projection
`PseudoPullback.fst G F` is a category fibred in groupoids over `C/U`.

The total category and projection are definitionally `BasedCategory.PseudoPullback G F` and
`BasedCategory.PseudoPullback.fst G F`; only the Prop-valued groupoid-fibredness witness is
added. -/
@[stacks 02Y6]
def fstGroupoids
    {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
    (F : X ⥤ᵇ Y) [Functor.IsFibered.InGroupoids X.p]
    [Functor.IsFibered.InGroupoids Y.p] {U : C}
    (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ Y) :
    FiberedCategoryOver.Groupoids (Over U) :=
  @FiberedCategoryOver.Groupoids.ofFunctor _ _ _ _ (fst G F).toFunctor
    (Fst.inGroupoids G F)

/-- The total category of `fstGroupoids F G` is the explicit heterogeneous pseudo-pullback. -/
@[simp]
theorem fstGroupoids.total
    {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
    (F : X ⥤ᵇ Y) [Functor.IsFibered.InGroupoids X.p]
    [Functor.IsFibered.InGroupoids Y.p] {U : C}
    (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ Y) :
    (fstGroupoids F G).total = (PseudoPullback G F).obj := sorry

/-- The projection of `fstGroupoids F G` is the first projection of the explicit
heterogeneous pseudo-pullback. -/
@[simp]
theorem fstGroupoids.p
    {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
    (F : X ⥤ᵇ Y) [Functor.IsFibered.InGroupoids X.p]
    [Functor.IsFibered.InGroupoids Y.p] {U : C}
    (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ Y) :
    (fstGroupoids F G).p = (fst G F).toFunctor := sorry

end BasedCategory.PseudoPullback

end CategoryTheory
