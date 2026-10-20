/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.DescentData.Chosen
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.DescentData.FiberedCategoryOver.Action
public import ReasLib.CategoryTheory.Sites.Cover.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Descent-data action over a bundled cover

A cartesian based functor acts on descent data for the arrow family of every bundled cover.  This
is a cover-indexed specialization of the general selected-cleavage action; it does not require a
stack condition on either projection.

## Main declarations

* `CategoryTheory.CartesianBasedFunctor.Descent.Cover.functor` is the universe-polymorphic owner.
* `CategoryTheory.FiberedCategoryOver.Descent.Cover.functor` is the fixed-owner specialization.
-/

@[expose] public section

universe v₁ u₁ uS₁ vS₁ uS₂ vS₂

namespace CategoryTheory

open Functor Limits

variable {C : Type u₁} [Category.{v₁} C]

namespace CartesianBasedFunctor.Descent

/-- The descent-data functor on the arrow family of a cover induced by a universe-polymorphic
cartesian based functor. -/
@[stacks 026F "cartesian functor action on cover descent data"]
noncomputable abbrev Cover.functor
    {S₁ : Type uS₁} {S₂ : Type uS₂}
    [Category.{vS₁} S₁] [Category.{vS₂} S₂]
    {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}
    [p₁.IsFibered] [p₂.IsFibered]
    (F : CartesianBasedFunctor p₁ p₂)
    {J : GrothendieckTopology C} {U : C} (T : J.Cover U) :
    (Functor.fiberPseudofunctor p₁).DescentData
        (fun I : T.Arrow ↦ I.f) ⥤
      (Functor.fiberPseudofunctor p₂).DescentData
        (fun I : T.Arrow ↦ I.f) :=
  chosen.functor (fun I : T.Arrow ↦ I.f) F

end CartesianBasedFunctor.Descent

namespace FiberedCategoryOver.Descent

variable {A B : FiberedCategoryOver C}

/-- The descent-data functor induced by a fibred-category morphism for the arrow family of a
cover. -/
@[stacks 026F "fibred-category morphism action on cover descent data"]
noncomputable abbrev Cover.functor
    (H : A ⟶ B) {J : GrothendieckTopology C} {U : C} (T : J.Cover U) :
    (Functor.fiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f) ⥤
      (Functor.fiberPseudofunctor B.p).DescentData (fun I : T.Arrow ↦ I.f) :=
  CartesianBasedFunctor.Descent.Cover.functor
    (FiberedCategoryOver.toCartesianBasedFunctor H) T

end FiberedCategoryOver.Descent

end CategoryTheory
