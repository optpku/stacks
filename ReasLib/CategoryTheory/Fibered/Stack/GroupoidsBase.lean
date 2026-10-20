/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids

/-!
# The identity fibration as a stack

The universe-resized identity fibration is a stack in groupoids on every site.
-/

@[expose] public section

universe u v w

namespace CategoryTheory.FiberedCategoryOver.Groupoids

/-- The universe-resized identity fibration is a stack in groupoids for every
Grothendieck topology on the base category. -/
instance base.isStackInGroupoids {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    IsStack.InGroupoids J (base.{u, v, w} C).p :=
  sorry

end CategoryTheory.FiberedCategoryOver.Groupoids
