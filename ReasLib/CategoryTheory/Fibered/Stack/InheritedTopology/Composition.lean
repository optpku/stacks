/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.InheritedTopology
public import ReasLib.CategoryTheory.Fibered.Stack.Basic
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids

/-!
# Composition of stacks for inherited topologies

Stack conditions compose when the intermediate category is equipped with the topology inherited
from its projection to the base site. The statement is formulated for arbitrary projection
functors, independently of bundled categories of stacks.

## Main declaration

* `CategoryTheory.IsStack.OnSite.comp_of_inheritedTopology` -- composition of a stack over a base
  site with a stack over its inherited topology.
* `CategoryTheory.IsStack.InSetoids.comp_of_inheritedTopology` -- the corresponding closure
  theorem for stacks in setoids.
* `CategoryTheory.IsStack.InSets.comp_of_inheritedTopology` -- the corresponding closure theorem
  for stacks in sets.
* `CategoryTheory.IsStack.InGroupoids.of_comp_inheritedTopology` -- recover the relative
  stack-in-groupoids condition from the base and composite conditions.
-/

@[expose] public section

universe uC uX uY vC vX vY

namespace CategoryTheory

namespace IsStack.OnSite

variable {C : Type uC} [Category.{vC} C]
variable {X : Type uX} [Category.{vX} X]
variable {Y : Type uY} [Category.{vY} Y]

/-- Lemma 8.10.6 (tag 09WX): if `p : X ⥤ C` is a stack over `(C, J)` and
`q : Y ⥤ X` is a stack for the topology on `X` inherited along `p`, then the composite
`q ⋙ p : Y ⥤ C` is a stack over `(C, J)`.

The theorem is registered as an instance because the inherited topology canonically determines
the intermediate stack condition. -/
@[stacks 09WX, instance]
theorem comp_of_inheritedTopology
    {J : GrothendieckTopology C} (p : X ⥤ C) (q : Y ⥤ X)
    [IsStack.OnSite J p] [IsStack.OnSite (p.inheritedTopology J) q] :
    IsStack.OnSite J (q ⋙ p) := sorry

end IsStack.OnSite

namespace IsStack.InGroupoids

variable {C : Type uC} [Category.{vC} C]
variable {X : Type uX} [Category.{vX} X]
variable {Y : Type uY} [Category.{vY} Y]

/-- Lemma 8.10.6 (tag 09WX), groupoid form: stack-in-groupoids conditions compose across the
topology inherited by the intermediate projection. -/
@[stacks 09WX, instance]
theorem comp_of_inheritedTopology
    {J : GrothendieckTopology C} (p : Functor X C) (q : Functor Y X)
    [IsStack.InGroupoids J p]
    [IsStack.InGroupoids (p.inheritedTopology J) q] :
    IsStack.InGroupoids J (q ⋙ p) := sorry

/-- If `p : X ⥤ C` and `q ⋙ p : Y ⥤ C` are stacks in groupoids over `(C, J)`, and
`q : Y ⥤ X` is fibered in groupoids, then `q` is a stack in groupoids for the topology on
`X` inherited along `p`. This is the projection-level form of Lemma 8.10.5. -/
@[stacks 06NX]
theorem of_comp_inheritedTopology
    {J : GrothendieckTopology C} (p : X ⥤ C) (q : Y ⥤ X)
    [IsStack.InGroupoids J p] [IsStack.InGroupoids J (q ⋙ p)]
    [Functor.IsFibered.InGroupoids q] :
    IsStack.InGroupoids (p.inheritedTopology J) q := sorry

end IsStack.InGroupoids

namespace IsStack.InSetoids

variable {C : Type uC} [Category.{vC} C]
variable {X : Type uX} [Category.{vX} X]
variable {Y : Type uY} [Category.{vY} Y]

/-- Lemma 8.10.6 (tag 09WX), setoid form: stacks in setoids compose when the intermediate
category carries the topology inherited from its projection to the base site. -/
@[stacks 09WX, instance]
theorem comp_of_inheritedTopology
    {J : GrothendieckTopology C} (p : X ⥤ C) (q : Y ⥤ X)
    [IsStack.InSetoids J p]
    [IsStack.InSetoids (p.inheritedTopology J) q] :
    IsStack.InSetoids J (q ⋙ p) := sorry

end IsStack.InSetoids

namespace IsStack.InSets

variable {C : Type uC} [Category.{vC} C]
variable {X : Type uX} [Category.{vX} X]
variable {Y : Type uY} [Category.{vY} Y]

/-- Lemma 8.10.6 (tag 09WX), set form: stacks in sets compose when the intermediate category
carries the topology inherited from its projection to the base site. -/
@[stacks 09WX, instance]
theorem comp_of_inheritedTopology
    {J : GrothendieckTopology C} (p : X ⥤ C) (q : Y ⥤ X)
    [IsStack.InSets J p]
    [IsStack.InSets (p.inheritedTopology J) q] :
    IsStack.InSets J (q ⋙ p) := sorry

end IsStack.InSets

end CategoryTheory
