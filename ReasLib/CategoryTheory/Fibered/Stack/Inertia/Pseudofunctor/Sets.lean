/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Computations
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Setoids
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Sets.AbsoluteMaps
import Mathlib.Tactic.CrossRefAttribute

/-!
# The inertia pseudofunctor on stacks in sets

This restriction retains the complete `1`-cell, `2`-cell, and coherence action of setoid-stack
inertia. Object membership uses direct discrete-fibration closure.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Sets.Inertia

variable (J : GrothendieckTopology C)

/-- Setoid-stack inertia preserves the object property selecting stacks in sets. -/
@[stacks 04Z4 "set-stack inertia object-property closure"]
theorem map_mem
    (X : StackOver.Setoids.{u, v, w, vS} J)
    (hX : IsStack.InSets.objectProperty J X) :
    IsStack.InSets.objectProperty J
      ((StackOver.Setoids.Inertia.strictPseudofunctor J).obj X) := sorry

/-- Absolute inertia as the canonical strict pseudofunctor on stacks in sets. -/
@[stacks 04Z4 "strict set-stack absolute-inertia pseudofunctor"]
def strictPseudofunctor :
    StrictPseudofunctor
      (StackOver.Sets.{u, v, w, vS} J)
      (StackOver.Sets.{u, v, max w vS, vS} J) :=
  ObjectProperty.FullSubbicategory.map
    (StackOver.Setoids.Inertia.strictPseudofunctor J)
    (map_mem J)

/-- The ordinary pseudofunctor view of absolute inertia on stacks in sets. -/
@[stacks 04Z4 "set-stack absolute-inertia pseudofunctor"]
def pseudofunctor :
    Pseudofunctor
      (StackOver.Sets.{u, v, w, vS} J)
      (StackOver.Sets.{u, v, max w vS, vS} J) :=
  (strictPseudofunctor J).toPseudofunctor

end StackOver.Sets.Inertia

end CategoryTheory
