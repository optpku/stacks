module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Basic.Objects
import Mathlib.Tactic.CrossRefAttribute

/-!
# Owner comparisons for inertia of stacks

These equations compare bundled stack inertia with the neutral `FiberedCategoryOver` owners.
They provide stable rewrite points without turning deferred equality proofs into data.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory.StackOver

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/-- Forgetting the stack proof from bundled relative inertia recovers the neutral
fibered-category owner. -/
@[simp, stacks 036Y "underlying relative-inertia stack"]
theorem relativeInertia.toFiberedCategoryOver
    {X Y : StackOver.{u, v, w, vS} J} (F : X ⟶ Y) :
    (relativeInertia F).toFiberedCategoryOver =
      FiberedCategoryOver.relativeInertia (Hom.toMor F) := sorry

/-- Forgetting the stack proof from bundled absolute inertia recovers the neutral
fibered-category owner. -/
@[simp, stacks 036Y "underlying absolute-inertia stack"]
theorem inertia.toFiberedCategoryOver (X : StackOver.{u, v, w, vS} J) :
    (inertia X).toFiberedCategoryOver =
      FiberedCategoryOver.inertia X.toFiberedCategoryOver := sorry

end CategoryTheory.StackOver
