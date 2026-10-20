module

public import ReasLib.CategoryTheory.Fibered.Stack.Pullback.Pseudofunctor.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Object computations for fixed-base pullback on stacks

This leaf records the neutral fibred category and base projection underlying a bundled stack
pullback.
-/

@[expose] public section

noncomputable section

universe uC uD uS vC vD vS

namespace CategoryTheory.StackOver

open CategoryTheory Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

/-- Forgetting a precoverage-presented stack pullback recovers the neutral fibred-category
pullback. -/
@[simp, stacks 04WC "underlying precoverage-presented fibred pullback"]
theorem pullbackOfPrecoverage.toFiberedCategoryOver
    (P : Precoverage C) {Q : Precoverage D} (u : C ⥤ D)
    (T : StackOver.{uD, vD, uS, vS} Q.toGrothendieck)
    [P.HasIsos] [P.HasPullbacks] [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [Functor.Precoverage.IsContinuous u P Q] :
    (StackOver.pullbackOfPrecoverage P u T).toFiberedCategoryOver =
      FiberedCategoryOver.pullback u T.toFiberedCategoryOver := sorry

/-- The total category of a precoverage-presented stack pullback is the defining categorical
pullback. -/
@[simp, stacks 04WC "precoverage-presented stack pullback total category"]
theorem pullbackOfPrecoverage.total
    (P : Precoverage C) {Q : Precoverage D} (u : C ⥤ D)
    (T : StackOver.{uD, vD, uS, vS} Q.toGrothendieck)
    [P.HasIsos] [P.HasPullbacks] [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [Functor.Precoverage.IsContinuous u P Q] :
    (StackOver.pullbackOfPrecoverage P u T).total =
      Limits.CategoricalPullback u T.p := sorry

/-- The projection of a precoverage-presented stack pullback is the first categorical-pullback
projection. -/
@[simp, stacks 04WC "precoverage-presented stack pullback projection"]
theorem pullbackOfPrecoverage.p
    (P : Precoverage C) {Q : Precoverage D} (u : C ⥤ D)
    (T : StackOver.{uD, vD, uS, vS} Q.toGrothendieck)
    [P.HasIsos] [P.HasPullbacks] [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [Functor.Precoverage.IsContinuous u P Q] :
    (StackOver.pullbackOfPrecoverage P u T).p =
      Limits.CategoricalPullback.π₁ u T.p := sorry

/-- Forgetting the bundled stack pullback recovers the canonical fibred-category pullback. -/
@[simp, stacks 04WC "underlying fibred-category pullback"]
theorem pullback_toFiberedCategoryOver
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (u : C ⥤ D) (T : StackOver.{uD, vD, uS, vS} K)
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] [u.IsContinuous J K] :
    (StackOver.pullback (J := J) (K := K) u T).toFiberedCategoryOver =
      FiberedCategoryOver.pullback u T.toFiberedCategoryOver := sorry

/-- Lemma 8.12.2 (tag 04WC): the total category of a bundled stack pullback is the defining
categorical pullback. -/
@[simp, stacks 04WC "stack pullback total category"]
theorem pullback_total
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (u : C ⥤ D) (T : StackOver.{uD, vD, uS, vS} K)
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] [u.IsContinuous J K] :
    (StackOver.pullback (J := J) (K := K) u T).total =
      Limits.CategoricalPullback u T.p := sorry

/-- The projection of a bundled stack pullback is the first categorical-pullback projection. -/
@[simp, stacks 04WC "stack pullback projection"]
theorem pullback_p
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (u : C ⥤ D) (T : StackOver.{uD, vD, uS, vS} K)
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] [u.IsContinuous J K] :
    (StackOver.pullback (J := J) (K := K) u T).p =
      Limits.CategoricalPullback.π₁ u T.p := sorry

end CategoryTheory.StackOver
