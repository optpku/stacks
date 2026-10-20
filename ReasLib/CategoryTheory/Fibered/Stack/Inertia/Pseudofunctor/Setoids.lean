/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Computations
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Groupoids
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Setoids
import Mathlib.Tactic.CrossRefAttribute

/-!
# The inertia pseudofunctor on stacks in setoids

This module restricts the groupoid-stack inertia pseudofunctor to thin fibres. The construction
preserves the complete `1`-cell, `2`-cell, and coherence action while adding only the
setoid-fibre closure witness.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Setoids.Inertia

variable (J : GrothendieckTopology C)

/-- Groupoid-stack inertia preserves the object property selecting stacks in setoids. -/
@[stacks 04Z4 "setoid-stack inertia object-property closure"]
theorem map_mem
    (X : StackOver.Groupoids.{u, v, w, vS} J)
    (hX : IsStack.InSetoids.objectProperty J X) :
    IsStack.InSetoids.objectProperty J
      ((StackOver.Groupoids.Inertia.strictPseudofunctor J).obj X) := sorry

/-- Absolute inertia as the canonical strict pseudofunctor on stacks in setoids. -/
@[stacks 04Z4 "strict setoid-stack absolute-inertia pseudofunctor"]
def strictPseudofunctor :
    StrictPseudofunctor
      (StackOver.Setoids.{u, v, w, vS} J)
      (StackOver.Setoids.{u, v, max w vS, vS} J) :=
  ObjectProperty.FullSubbicategory.map
    (StackOver.Groupoids.Inertia.strictPseudofunctor J)
    (map_mem J)

/-- The ordinary pseudofunctor view of absolute inertia on stacks in setoids. -/
@[stacks 04Z4 "setoid-stack absolute-inertia pseudofunctor"]
def pseudofunctor :
    Pseudofunctor
      (StackOver.Setoids.{u, v, w, vS} J)
      (StackOver.Setoids.{u, v, max w vS, vS} J) :=
  (strictPseudofunctor J).toPseudofunctor

end StackOver.Setoids.Inertia

end CategoryTheory
