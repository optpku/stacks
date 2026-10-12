/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero objects in categories of actions

The forgetful functor from bundled actions detects zero objects.  This small bridge is useful
whenever an adjunction transfers injective or projective constructions to an action category.
-/

@[expose] public section

universe w v u

open CategoryTheory.Limits

namespace CategoryTheory.Action

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]
variable {G : Type w} [Monoid G]

/-- If the underlying object of an action is zero, then the action itself is zero. -/
@[stacks 04JF "action forgetful functor detects zero"]
theorem isZero_of_forget_obj_isZero (X : Action V G)
    (hX : IsZero ((Action.forget V G).obj X)) : IsZero X := sorry

end CategoryTheory.Action
