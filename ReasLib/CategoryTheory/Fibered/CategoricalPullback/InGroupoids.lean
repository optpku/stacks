/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Cleavage
public import ReasLib.CategoryTheory.Fibered.InGroupoids

/-!
# Categorical pullbacks of categories fibred in groupoids

The first projection of a categorical pullback of a category fibred in groupoids is again
fibred in groupoids.  This statement is independent of topologies and is the structural input
for pullback of stacks in groupoids.
-/

@[expose] public section

universe uC uD uS vC vD vS

namespace CategoryTheory

open Limits

namespace Limits.CategoricalPullback

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

namespace Left

/-- The first projection of a categorical pullback of a category fibred in groupoids is
canonically fibred in groupoids. -/
@[stacks 04WD "categorical pullback remains fibred in groupoids"]
instance isFiberedInGroupoids
    (u : C ⥤ D) (p : S ⥤ D) [Functor.IsFibered.InGroupoids p] :
    Functor.IsFibered.InGroupoids (π₁ u p) := sorry

end Left

end Limits.CategoricalPullback

end CategoryTheory
