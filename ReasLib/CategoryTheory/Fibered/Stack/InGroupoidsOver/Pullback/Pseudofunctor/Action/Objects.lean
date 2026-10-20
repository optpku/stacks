module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Pullback.Pseudofunctor.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Object computations for fixed-base pullback on stacks in groupoids

This leaf records the groupoid-fibred, ordinary-stack, total-category, and projection readouts
of a bundled pullback.
-/

@[expose] public section

noncomputable section

universe uC uD uS vC vD vS

namespace CategoryTheory.StackOver.Groupoids

open CategoryTheory Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Forgetting a precoverage-presented groupoid-stack pullback recovers the neutral
groupoid-fibred pullback. -/
@[simp, stacks 04WD "underlying precoverage-presented groupoid pullback"]
theorem pullbackOfPrecoverage.toGroupoids
    (P : Precoverage C) {Q : Precoverage D} (u : C ⥤ D)
    (T : StackOver.Groupoids.{uD, vD, uS, vS} Q.toGrothendieck)
    [P.HasIsos] [P.HasPullbacks] [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [Functor.Precoverage.IsContinuous u P Q] :
    (pullbackOfPrecoverage P u T).toGroupoids =
      FiberedCategoryOver.Groupoids.pullback u T.toGroupoids := sorry

/-- Forgetting groupoid fibers from a precoverage-presented pullback recovers the ordinary
precoverage-presented stack pullback. -/
@[simp, stacks 04WD "underlying ordinary precoverage groupoid pullback"]
theorem pullbackOfPrecoverage.toStackOver
    (P : Precoverage C) {Q : Precoverage D} (u : C ⥤ D)
    (T : StackOver.Groupoids.{uD, vD, uS, vS} Q.toGrothendieck)
    [P.HasIsos] [P.HasPullbacks] [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [Functor.Precoverage.IsContinuous u P Q] :
    (pullbackOfPrecoverage P u T).toStackOver =
      StackOver.pullbackOfPrecoverage P u T.toStackOver := sorry

/-- The total category of a precoverage-presented groupoid-stack pullback is the defining
categorical pullback. -/
@[simp, stacks 04WD "precoverage groupoid-stack pullback total category"]
theorem pullbackOfPrecoverage.total
    (P : Precoverage C) {Q : Precoverage D} (u : C ⥤ D)
    (T : StackOver.Groupoids.{uD, vD, uS, vS} Q.toGrothendieck)
    [P.HasIsos] [P.HasPullbacks] [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [Functor.Precoverage.IsContinuous u P Q] :
    (pullbackOfPrecoverage P u T).total = CategoricalPullback u T.p := sorry

/-- The projection of a precoverage-presented groupoid-stack pullback is the first
categorical-pullback projection. -/
@[simp, stacks 04WD "precoverage groupoid-stack pullback projection"]
theorem pullbackOfPrecoverage.p
    (P : Precoverage C) {Q : Precoverage D} (u : C ⥤ D)
    (T : StackOver.Groupoids.{uD, vD, uS, vS} Q.toGrothendieck)
    [P.HasIsos] [P.HasPullbacks] [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [Functor.Precoverage.IsContinuous u P Q] :
    (pullbackOfPrecoverage P u T).p = CategoricalPullback.π₁ u T.p := sorry

/-- Forgetting the stack condition from a groupoid-stack pullback recovers the canonical
groupoid-fibred pullback. -/
@[simp, stacks 04WD "underlying groupoid-stack pullback"]
theorem pullback_toGroupoids
    (u : C ⥤ D) (T : StackOver.Groupoids.{uD, vD, uS, vS} K)
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] [u.IsContinuous J K] :
    (pullback (J := J) (K := K) u T).toGroupoids =
      FiberedCategoryOver.Groupoids.pullback u T.toGroupoids := sorry

/-- Forgetting the groupoid-fibre refinement from a groupoid-stack pullback recovers the ordinary
bundled stack pullback. -/
@[simp, stacks 04WD "underlying ordinary stack pullback"]
theorem pullback_toStackOver
    (u : C ⥤ D) (T : StackOver.Groupoids.{uD, vD, uS, vS} K)
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] [u.IsContinuous J K] :
    (pullback (J := J) (K := K) u T).toStackOver =
      StackOver.pullback (J := J) (K := K) u T.toStackOver := sorry

/-- The total category of a bundled groupoid-stack pullback is the defining categorical
pullback. -/
@[simp, stacks 04WD "groupoid-stack pullback total category"]
theorem pullback_total
    (u : C ⥤ D) (T : StackOver.Groupoids.{uD, vD, uS, vS} K)
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] [u.IsContinuous J K] :
    (pullback (J := J) (K := K) u T).total = CategoricalPullback u T.p := sorry

/-- The projection of a bundled groupoid-stack pullback is the first categorical-pullback
projection. -/
@[simp, stacks 04WD "groupoid-stack pullback projection"]
theorem pullback_p
    (u : C ⥤ D) (T : StackOver.Groupoids.{uD, vD, uS, vS} K)
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] [u.IsContinuous J K] :
    (pullback (J := J) (K := K) u T).p = CategoricalPullback.π₁ u T.p := sorry

end CategoryTheory.StackOver.Groupoids
