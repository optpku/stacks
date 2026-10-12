/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Endofunctor.MonadResolution.Augmentation
public import ReasLib.AlgebraicTopology.CosimplicialObject.Augmented.Composition.Pointwise
import Mathlib.Tactic.CrossRefAttribute

/-!
# Evaluating canonical monad resolutions

This leaf evaluates the augmented resolution functorially in both the monad and the resolved
object. It exposes degree and morphism formulas without forcing evaluation dependencies on
users of the canonical functor-level construction.
-/

@[expose] public section

open CategoryTheory.CosimplicialObject
open CategoryTheory.Functor
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Monad

variable (T : Monad C)

/-- Evaluated augmented monad resolutions, functorial in the monad and resolved object. -/
@[stacks 0G5N "bifunctorial evaluated monad resolution"]
noncomputable def cosimplicialResolution.evalFunctor :
    Monad C ⥤ C ⥤ CosimplicialObject.Augmented C :=
  cosimplicialResolution.augmentedFunctor ⋙
    CosimplicialObject.Augmented.pointwiseFunctor

/-- Evaluation of the augmented monad resolution, functorial in the resolved object. -/
@[stacks 0G5N "evaluated monad resolution functor"]
noncomputable def cosimplicialResolution.eval :
    C ⥤ CosimplicialObject.Augmented C :=
  (cosimplicialResolution.evalFunctor (C := C)).obj T

/-- The monad-variable action of evaluated resolutions is pointwise evaluation of the
corresponding augmented resolution map. -/
@[simp]
theorem cosimplicialResolution.evalFunctor.map {T S : Monad C} (alpha : T ⟶ S) :
    (cosimplicialResolution.evalFunctor (C := C)).map alpha =
      CosimplicialObject.Augmented.Pointwise.hom
        (cosimplicialResolution.augmentedMap alpha) := sorry

/-- The degree-`n` object of an evaluated monad resolution is the positive `n + 1` iterate. -/
@[stacks 0G5N "evaluated monad resolution degree"]
theorem cosimplicialResolution.eval.degree (X : C) (n : ℕ) :
    ((cosimplicialResolution.eval T).obj X).right.obj ⦋n⦌ =
      T.toFunctor ⁺⦋n⦌.obj X := sorry

/-- In cosimplicial degree `Δ`, evaluation sends `f` by the corresponding endofunctor
iterate. -/
@[simp, stacks 0G5N "evaluated monad resolution map formula"]
theorem cosimplicialResolution.eval.map.right.app
    {X Y : C} (f : X ⟶ Y) (Δ : SimplexCategory) :
    ((cosimplicialResolution.eval T).map f).right.app Δ =
      T.toFunctor ⁺⦋Δ.len⦌.map f := sorry

/-- On coaugmentation points, evaluation sends `f` by the identity endofunctor. -/
@[simp, stacks 0G5N "evaluated monad coaugmentation-point map formula"]
theorem cosimplicialResolution.eval.map.left {X Y : C} (f : X ⟶ Y) :
    ((cosimplicialResolution.eval T).map f).left = f := sorry

end Monad

end CategoryTheory
