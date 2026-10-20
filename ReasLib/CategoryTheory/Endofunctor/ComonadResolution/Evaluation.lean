/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Endofunctor.ComonadResolution.Augmentation
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.Composition.Pointwise
import Mathlib.Tactic.CrossRefAttribute

/-!
# Evaluating canonical comonad resolutions

This leaf evaluates the augmented resolution functorially in both the comonad and the resolved
object. It exposes degree and morphism formulas without forcing evaluation dependencies on
users of the canonical functor-level construction.
-/

@[expose] public section

open Opposite
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Augmentation
open CategoryTheory.Functor
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe v u v' u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Comonad

variable (G : Comonad C)

/-- Evaluated augmented resolutions, functorial in both the comonad and the resolved object. -/
@[stacks 0G5N "bifunctorial evaluated comonad resolution"]
noncomputable def simplicialResolution.evalFunctor :
    Comonad C ⥤ C ⥤ SimplicialObject.Augmented C :=
  simplicialResolution.augmentedFunctor ⋙
    SimplicialObject.Augmented.pointwiseFunctor

/-- Evaluation of the augmented comonad resolution, functorial in the resolved object. -/
@[stacks 0G5N "evaluated comonad resolution functor"]
noncomputable def simplicialResolution.eval : C ⥤ SimplicialObject.Augmented C :=
  (simplicialResolution.evalFunctor (C := C)).obj G

/-- The comonad-variable action of evaluated resolutions is pointwise evaluation of the
corresponding augmented resolution map. -/
@[simp, stacks 0G5N "comonad-variable map of evaluated resolutions"]
theorem simplicialResolution.evalFunctor.map {G H : Comonad C} (α : G ⟶ H) :
    (simplicialResolution.evalFunctor (C := C)).map α =
      SimplicialObject.Augmented.Pointwise.hom
        (simplicialResolution.augmentedMap α) := sorry

/-- The degree-`n` object of an evaluated comonad resolution is the positive `n + 1` iterate. -/
@[stacks 0G5N "evaluated comonad resolution degree"]
theorem simplicialResolution.eval.degree (X : C) (n : ℕ) :
    ((simplicialResolution.eval G).obj X).left.obj (op ⦋n⦌) =
      G.toFunctor ⁺⦋n⦌.obj X := sorry

/-- On simplicial degree `Δ`, evaluation sends `f` by the corresponding iterated endofunctor. -/
@[simp, stacks 0G5N "evaluated comonad resolution map formula"]
theorem simplicialResolution.eval.map.left.app
    {X Y : C} (f : X ⟶ Y) (Δ : SimplexCategoryᵒᵖ) :
    ((simplicialResolution.eval G).map f).left.app Δ =
      G.toFunctor ⁺⦋Δ.unop.len⦌.map f := sorry

/-- On augmentation points, evaluation sends `f` by the identity endofunctor. -/
@[simp, stacks 0G5N "evaluated comonad augmentation-point map formula"]
theorem simplicialResolution.eval.map.right {X Y : C} (f : X ⟶ Y) :
    ((simplicialResolution.eval G).map f).right = f := sorry

end Comonad

end CategoryTheory
