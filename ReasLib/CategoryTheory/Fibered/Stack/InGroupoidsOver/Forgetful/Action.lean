/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# Object and morphism actions of the groupoid-stack forgetful pseudofunctor

This file exposes stable object and `1`-cell projections of
`StackOver.Groupoids.forget J` through the groupoid-fibred, based-category, total-category,
and fiber views.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Groupoids

variable {J : GrothendieckTopology C}

namespace forget

/-- Forgetting the stack condition gives the canonical underlying groupoid-fibred category. -/
@[simp, stacks 02ZK "groupoid-stack forgetful object"]
theorem obj (X : StackOver.Groupoids.{u, v, w, vS} J) :
    (StackOver.Groupoids.forget J).obj X = X.toGroupoids := sorry

/-- Forgetting the stack condition retains the underlying based category. -/
@[simp, stacks 02ZK "groupoid-stack forgetful based category"]
theorem obj.toBasedCategory (X : StackOver.Groupoids.{u, v, w, vS} J) :
    ((StackOver.Groupoids.forget J).obj X).toBasedCategory =
      X.toBasedCategory := sorry

/-- Forgetting the stack condition retains the total category. -/
@[simp, stacks 02ZK "groupoid-stack forgetful total category"]
theorem obj.total (X : StackOver.Groupoids.{u, v, w, vS} J) :
    ((StackOver.Groupoids.forget J).obj X).total = X.total := sorry

/-- Forgetting the stack condition retains the projection to the base. -/
@[simp, stacks 02ZK "groupoid-stack forgetful projection"]
theorem obj.p (X : StackOver.Groupoids.{u, v, w, vS} J) :
    ((StackOver.Groupoids.forget J).obj X).p = X.p := sorry

/-- The mapped groupoid-fibred morphism is the canonical ambient projection of the stack
morphism. -/
@[simp, stacks 02ZK "groupoid-stack forgetful morphism"]
theorem map.toGroupoidsMor
    {X Y : StackOver.Groupoids.{u, v, w, vS} J} (F : X ⟶ Y) :
    (StackOver.Groupoids.forget J).map F = Hom.toGroupoidsMor F := sorry

/-- The based functor underlying a mapped stack morphism is its canonical based-functor
projection. -/
@[simp, stacks 02ZK "groupoid-stack forgetful based functor"]
theorem map.toBasedFunctor
    {X Y : StackOver.Groupoids.{u, v, w, vS} J} (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedFunctor
        ((StackOver.Groupoids.forget J).map F) =
      Hom.toBasedFunctor F := sorry

/-- The total functor underlying a mapped stack morphism is its canonical total-functor
projection. -/
@[simp, stacks 02ZK "groupoid-stack forgetful total functor"]
theorem map.toFunctor
    {X Y : StackOver.Groupoids.{u, v, w, vS} J} (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toFunctor
        ((StackOver.Groupoids.forget J).map F) =
      Hom.toFunctor F := sorry

/-- The fiber functor underlying a mapped stack morphism is its canonical fiber action. -/
@[simp, stacks 02ZK "groupoid-stack forgetful fiber functor"]
theorem map.fiberFunctor
    {X Y : StackOver.Groupoids.{u, v, w, vS} J}
    (F : X ⟶ Y) (U : C) :
    FiberedCategoryOver.Groupoids.fiberFunctor
        ((StackOver.Groupoids.forget J).map F) U =
      Hom.fiberFunctor F U := sorry

end forget

end StackOver.Groupoids

end CategoryTheory
