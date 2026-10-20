/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Setoids.Objects
import Mathlib.Tactic.CrossRefAttribute

/-!
# Owner comparisons for inertia of setoid stacks

Named equations expose both the groupoid-stack owner and the setoid-fibred owner of bundled
setoid-stack inertia without turning deferred equality proofs into data.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory.StackOver.Setoids

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/-- The groupoid-stack view of bundled relative inertia is the neutral groupoid-stack owner. -/
@[simp, stacks 036Y "underlying groupoid-stack relative inertia"]
theorem relativeInertia.toGroupoids
    {X Y : StackOver.Setoids.{u, v, w, vS} J} (F : X ⟶ Y) :
    (relativeInertia F).toGroupoids =
      StackOver.Groupoids.relativeInertia (Hom.toGroupoidsMor F) := sorry

/-- The setoid-fibred view of bundled relative inertia is the neutral setoid owner. -/
@[simp, stacks 036Y "underlying setoid-fibred relative inertia"]
theorem relativeInertia.toSetoids
    {X Y : StackOver.Setoids.{u, v, w, vS} J} (F : X ⟶ Y) :
    (relativeInertia F).toSetoids =
      FiberedCategoryOver.Setoids.relativeInertia (Hom.toSetoidsMor F) := sorry

/-- The groupoid-stack view of bundled absolute inertia is the neutral groupoid-stack owner. -/
@[simp, stacks 036Y "underlying groupoid-stack absolute inertia"]
theorem inertia.toGroupoids (X : StackOver.Setoids.{u, v, w, vS} J) :
    (inertia X).toGroupoids = StackOver.Groupoids.inertia X.toGroupoids := sorry

/-- The setoid-fibred view of bundled absolute inertia is the neutral setoid owner. -/
@[simp, stacks 036Y "underlying setoid-fibred absolute inertia"]
theorem inertia.toSetoids (X : StackOver.Setoids.{u, v, w, vS} J) :
    (inertia X).toSetoids = FiberedCategoryOver.Setoids.inertia X.toSetoids := sorry

end CategoryTheory.StackOver.Setoids
