/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.Closure.Object
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Pseudofunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Set-fibred inertia pseudofunctor construction

The universe-changing strict restriction of neutral based inertia to categories fibred in sets.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory.FiberedCategoryOver.Sets.Inertia

variable {C : Type u} [Category.{v} C]

variable (C) in
/-- Based inertia preserves the object property selecting set-fibred categories. -/
theorem map_mem
    (X : BasedCategory.{vS, w} C)
    (hX : BasedCategory.isFiberedInSets C X) :
    BasedCategory.isFiberedInSets C
      ((BasedCategory.Inertia.strictPseudofunctor C).obj X) := sorry

variable (C) in
/-- Absolute inertia as the canonical universe-changing strict pseudofunctor on categories
fibred in sets. The object-membership function is the direct discrete-fibration closure theorem,
while all object, `1`-cell, and `2`-cell data come from neutral based inertia. -/
@[stacks 04Z4 "strict set-fibred absolute inertia pseudofunctor"]
def strictPseudofunctor :
    StrictPseudofunctor
      (FiberedCategoryOver.Sets.{u, v, w, vS} C)
      (FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :=
  ObjectProperty.FullSubbicategory.map
    (BasedCategory.Inertia.strictPseudofunctor C)
    (map_mem C)

variable (C) in
/-- The ordinary pseudofunctor view of set-fibred absolute inertia. -/
@[stacks 04Z4 "set-fibred absolute inertia pseudofunctor"]
def pseudofunctor :
    Pseudofunctor
      (FiberedCategoryOver.Sets.{u, v, w, vS} C)
      (FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :=
  (strictPseudofunctor C).toPseudofunctor

end CategoryTheory.FiberedCategoryOver.Sets.Inertia
