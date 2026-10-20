/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsolutePseudofunctor
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Groupoids
import Mathlib.Tactic.CrossRefAttribute

/-!
# The inertia pseudofunctor on stacks in groupoids

This module restricts groupoid-fibred inertia to the full subbicategory selected by the stack
condition. Its typed action and coherence are inherited unchanged from the neutral owner.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Groupoids.Inertia

variable (J : GrothendieckTopology C)

/-- Groupoid-fibred inertia preserves the object property selecting stacks on the site. -/
@[stacks 04Z4 "groupoid-stack inertia object-property closure"]
theorem map_mem
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C)
    (hX : IsStack.InGroupoids.objectProperty J X) :
    IsStack.InGroupoids.objectProperty J
      ((FiberedCategoryOver.Groupoids.Inertia.strictPseudofunctor C).obj X) := sorry

/-- Absolute inertia as the canonical strict pseudofunctor on stacks in groupoids. -/
@[stacks 04Z4 "strict groupoid-stack absolute-inertia pseudofunctor"]
def strictPseudofunctor :
    StrictPseudofunctor
      (StackOver.Groupoids.{u, v, w, vS} J)
      (StackOver.Groupoids.{u, v, max w vS, vS} J) :=
  ObjectProperty.FullSubbicategory.map
    (FiberedCategoryOver.Groupoids.Inertia.strictPseudofunctor C)
    (map_mem J)

/-- The ordinary pseudofunctor view of absolute inertia on stacks in groupoids. -/
@[stacks 04Z4 "groupoid-stack absolute-inertia pseudofunctor"]
def pseudofunctor :
    Pseudofunctor
      (StackOver.Groupoids.{u, v, w, vS} J)
      (StackOver.Groupoids.{u, v, max w vS, vS} J) :=
  (strictPseudofunctor J).toPseudofunctor

end StackOver.Groupoids.Inertia

end CategoryTheory
