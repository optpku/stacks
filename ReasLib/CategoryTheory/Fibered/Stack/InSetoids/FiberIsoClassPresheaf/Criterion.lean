/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.Setoids.AssociatedSets.Basic
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids
import Mathlib.Tactic.CrossRefAttribute

/-!
# The stack criterion for fibrewise isomorphism classes

This leaf owns the projection-level criterion only.  The associated stack and its comparison
maps live in the sibling `AssociatedSets` leaves, so importing the criterion does not pull in the
full bundled construction.
-/

@[expose] public section

universe uC uS vC vS

namespace CategoryTheory

variable {C : Type uC} {S : Type uS} [Category.{vC} C] [Category.{vS} S]

namespace IsStack.InSetoids

/-- A category fibered in setoids is a stack over `(C, J)` exactly when its presheaf of
fiberwise isomorphism classes is a sheaf. -/
@[stacks 0432]
theorem iff_fiberIsoClass_isSheaf
    (J : GrothendieckTopology C) (p : S ⥤ C)
    [Functor.IsFibered.InSetoids p] :
    IsStack.InSetoids J p ↔
      Presheaf.IsSheaf J (Functor.fiberIsoClassPresheaf p) := sorry

/-- A setoid-fibred category is a stack exactly when its canonical associated category fibred in
sets is a stack.  Both sides use the same isomorphism-class presheaf, so no representatives are
chosen. -/
@[stacks 0432 "associated sets stack criterion"]
theorem iff_associatedSets
    (J : GrothendieckTopology C) (Z : FiberedCategoryOver.Setoids C) :
    IsStack.InSetoids J Z.p ↔ IsStack.InSets J Z.associatedSets.p := sorry

end IsStack.InSetoids

end CategoryTheory
