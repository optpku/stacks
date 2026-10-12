/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# The inertia pseudofunctor on stacks

This module restricts the neutral fibred inertia pseudofunctor to the full subbicategory of
stacks. The stack condition contributes only the object-membership witness; all `1`-cell,
`2`-cell, and coherence data are inherited from the neutral owner.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Inertia

variable (J : GrothendieckTopology C)

/-- Fibred inertia preserves the object property selecting stacks on the site. -/
@[stacks 04Z4 "stack inertia object-property closure"]
theorem map_mem
    (X : FiberedCategoryOver.{u, v, w, vS} C)
    (hX : IsStack.OnSite.objectProperty J X) :
    IsStack.OnSite.objectProperty J
      ((FiberedCategoryOver.Inertia.strictPseudofunctor C).obj X) := sorry

/-- Absolute inertia as the canonical strict pseudofunctor on stacks over a fixed site. -/
@[stacks 04Z4 "strict stack absolute-inertia pseudofunctor"]
def strictPseudofunctor :
    StrictPseudofunctor
      (StackOver.{u, v, w, vS} J)
      (StackOver.{u, v, max w vS, vS} J) :=
  ObjectProperty.FullSubbicategory.map
    (FiberedCategoryOver.Inertia.strictPseudofunctor C)
    (map_mem J)

/-- The ordinary pseudofunctor view of absolute inertia on stacks. -/
@[stacks 04Z4 "stack absolute-inertia pseudofunctor"]
def pseudofunctor :
    Pseudofunctor
      (StackOver.{u, v, w, vS} J)
      (StackOver.{u, v, max w vS, vS} J) :=
  (strictPseudofunctor J).toPseudofunctor

end StackOver.Inertia

end CategoryTheory
