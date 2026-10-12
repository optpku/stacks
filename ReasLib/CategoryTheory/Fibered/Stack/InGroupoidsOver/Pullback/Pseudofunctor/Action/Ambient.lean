/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Pullback.Pseudofunctor.Action.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ambient action computations for fixed-base pullback on stacks in groupoids

This leaf identifies the groupoid-fibred action before the stack condition is restored by the
full-subbicategory lift.
-/

@[expose] public section

noncomputable section

universe uC uD uS vC vD vS

namespace CategoryTheory.StackOver.Groupoids.Pullback

open CategoryTheory Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)
variable [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] [u.IsContinuous J K]

/-- The object action of the ambient pseudofunctor is the neutral groupoid-fibred pullback. -/
@[simp, stacks 04WD "ambient groupoid-stack pullback object"]
theorem ambient.obj (T : StackOver.Groupoids.{uD, vD, uS, vS} K) :
    (ambient K u).obj T =
      FiberedCategoryOver.Groupoids.pullback u T.toGroupoids := sorry

/-- The `1`-cell action of the ambient pseudofunctor is neutral pullback of the underlying
groupoid-fibred morphism. -/
@[simp, stacks 04WD "ambient groupoid-stack pullback morphism"]
theorem ambient.map
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K} (F : X ⟶ Y) :
    (ambient K u).map F =
      FiberedCategoryOver.Groupoids.Pullback.map u F.hom := sorry

/-- The `2`-cell action of the ambient pseudofunctor is neutral pullback of the underlying
groupoid-fibred `2`-morphism. -/
@[simp, stacks 04WD "ambient groupoid-stack pullback two-cell"]
theorem ambient.map₂
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (ambient K u).map₂ eta =
      FiberedCategoryOver.Groupoids.Pullback.map₂ u eta.hom := sorry

end CategoryTheory.StackOver.Groupoids.Pullback
