/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Thin Hom categories for stacks in setoids

The stack wrapper does not add `2`-morphism data. Thinness of the target's setoid fibres therefore
makes every Hom category thin, independently of descent. Nested induced bicategories, including
stacks in sets, inherit this fact through the generic induced-bicategory instance.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Setoids

variable {J : GrothendieckTopology C}

/-- Every Hom category of stacks in setoids is thin. -/
@[stacks 0433 "stack-in-setoids Hom categories are thin"]
instance homIsThin (X Y : StackOver.Setoids J) : Quiver.IsThin (X ⟶ Y) := sorry

end StackOver.Setoids

end CategoryTheory
