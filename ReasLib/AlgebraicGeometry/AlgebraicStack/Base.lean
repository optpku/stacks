/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The universe-resized identity fibration on `Over S` is an algebraic stack. -/
instance base (S : Scheme.{u}) :
    AlgebraicStack (FiberedCategoryOver.Groupoids.base.{u + 1, u, u + 1} (Over S)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
