/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Sets.Objects
import Mathlib.Tactic.CrossRefAttribute

/-!
# Owner comparisons for inertia of stacks in sets

These named equations compare the bundled stack-in-sets objects with their neutral setoid-stack
and set-fibred inertia models without turning deferred equality proofs into data.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory.StackOver.Sets

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/-- The setoid-stack view of relative inertia is the neutral setoid-stack owner. -/
@[simp, stacks 036Y "underlying setoid-stack relative inertia"]
theorem relativeInertia.toSetoids
    {X Y : StackOver.Sets.{u, v, w, vS} J} (F : X ⟶ Y) :
    (relativeInertia F).toSetoids =
      StackOver.Setoids.relativeInertia (Hom.toSetoidsMor F) := sorry

/-- The setoid-stack view of absolute inertia is the neutral setoid-stack owner. -/
@[simp, stacks 036Y "underlying setoid-stack absolute inertia"]
theorem inertia.toSetoids (X : StackOver.Sets.{u, v, w, vS} J) :
    (inertia X).toSetoids = StackOver.Setoids.inertia X.toSetoids := sorry

end CategoryTheory.StackOver.Sets
