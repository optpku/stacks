module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Groupoids.Objects
import Mathlib.Tactic.CrossRefAttribute

/-!
# Owner comparisons for inertia of groupoid stacks

Named equations compare bundled groupoid-stack inertia with the neutral groupoid-fibred owners
used by the lower layer, without turning deferred equality proofs into data.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory.StackOver.Groupoids

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/-- The groupoid-fibred view of bundled relative inertia is the neutral owner. -/
@[simp, stacks 036Y "underlying groupoid relative-inertia stack"]
theorem relativeInertia.toGroupoids
    {X Y : StackOver.Groupoids.{u, v, w, vS} J} (F : X ⟶ Y) :
    (relativeInertia F).toGroupoids =
      FiberedCategoryOver.Groupoids.relativeInertia (Hom.toGroupoidsMor F) := sorry

/-- The groupoid-fibred view of bundled absolute inertia is the neutral owner. -/
@[simp, stacks 036Y "underlying groupoid absolute-inertia stack"]
theorem inertia.toGroupoids (X : StackOver.Groupoids.{u, v, w, vS} J) :
    (inertia X).toGroupoids = FiberedCategoryOver.Groupoids.inertia X.toGroupoids := sorry

end CategoryTheory.StackOver.Groupoids
