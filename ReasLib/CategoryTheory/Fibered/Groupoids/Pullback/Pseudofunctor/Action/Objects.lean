/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Pullback.Pseudofunctor.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Object computations for fixed-base pullback in groupoids

This leaf records the neutral fibred category, total category, and projection underlying the
bundled groupoid-fibred pullback.
-/

@[expose] public section

noncomputable section

universe uC uD uS vC vD vS

namespace CategoryTheory.FiberedCategoryOver.Groupoids

open CategoryTheory Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

/-- Forgetting the groupoid-fibre refinement from the bundled pullback recovers the ordinary
fibred-category pullback. -/
@[simp, stacks 04WD "underlying fibred-category pullback"]
theorem pullback_toFibered
    (u : C ⥤ D) (X : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D) :
    (FiberedCategoryOver.Groupoids.toFibered C).obj (pullback u X) =
      FiberedCategoryOver.pullback u
        ((FiberedCategoryOver.Groupoids.toFibered D).obj X) := sorry

/-- The total category of a groupoid-fibred pullback is the defining categorical pullback. -/
@[simp, stacks 04WD "groupoid-fibred pullback total category"]
theorem pullback_total
    (u : C ⥤ D) (X : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D) :
    (pullback u X).total = CategoricalPullback u X.p := sorry

/-- The projection of the groupoid-fibred pullback is the first categorical-pullback projection. -/
@[simp, stacks 04WD "groupoid-fibred pullback projection"]
theorem pullback_p
    (u : C ⥤ D) (X : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D) :
    (pullback u X).p = CategoricalPullback.π₁ u X.p := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids

