module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Hom.Fibered.Computations
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Hom.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for the inverse-image Hom functor

This leaf exposes the ambient, based, total-category, fiberwise, and componentwise actions of the
inverse-image/direct-image Hom functor without requiring consumers to unfold its composite.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Limits
open scoped Bicategory

namespace StackOver.InverseImage

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {u : C ⥤ D}
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]
variable [u.IsContinuous J K]
variable {S : StackOver.{uC, vC,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
variable (I : StackOver.InverseImage K u S)
variable {T : StackOver.{uD, vD,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} K}

namespace homFunctor.obj

/-- Forgetting the bundled stack morphism produced on an object recovers the canonical
pushforward-pullback Hom construction applied after the inverse-image comparison. -/
@[simp, stacks 04WK "inverse-image Hom object computation"]
theorem toMor (F : I.target ⟶ T) :
    StackOver.Hom.toMor ((homFunctor I T).obj F) =
      FiberedCategoryOver.Pushforward.Hom.obj (hX := I.sourceChoice) u
        (I.comparisonHom ≫ StackOver.Hom.toMor F) := sorry

/-- The based functor underlying the object action is the canonical pullback comparison formed
after precomposing with the inverse-image stackification morphism. -/
@[simp, stacks 04WK "inverse-image Hom based computation"]
theorem toBasedFunctor (F : I.target ⟶ T) :
    StackOver.Hom.toBasedFunctor ((homFunctor I T).obj F) =
      FiberedCategoryOver.Pushforward.Precompose.obj (hX := I.sourceChoice) u
        (FiberedCategoryOver.toBasedFunctor
          (I.comparisonHom ≫ StackOver.Hom.toMor F)) := sorry

/-- The total-category functor underlying the object action is the categorical-pullback
comparison after precomposition with the inverse-image stackification morphism. -/
@[simp, stacks 04WK "inverse-image Hom total computation"]
theorem toFunctor (F : I.target ⟶ T) :
    StackOver.Hom.toFunctor ((homFunctor I T).obj F) =
      FiberedCategoryOver.Pushforward.Precompose.functor (hX := I.sourceChoice) u
        (FiberedCategoryOver.toBasedFunctor
          (I.comparisonHom ≫ StackOver.Hom.toMor F)) := sorry

/-- On the fiber over `U`, the object action is the fiber functor of the canonical based pullback
comparison after precomposition with the inverse-image stackification morphism. -/
@[simp, stacks 04WK "inverse-image Hom fiber computation"]
theorem fiberFunctor (F : I.target ⟶ T) (U : C) :
    StackOver.Hom.fiberFunctor ((homFunctor I T).obj F) U =
      (FiberedCategoryOver.Pushforward.Precompose.obj (hX := I.sourceChoice) u
        (FiberedCategoryOver.toBasedFunctor
          (I.comparisonHom ≫ StackOver.Hom.toMor F))).fiberFunctor U := sorry

end homFunctor.obj

namespace homFunctor.map

/-- Forgetting the bundled `2`-morphism produced by the Hom functor recovers the
pushforward-pullback Hom action on the left-whiskered ambient cell. -/
@[simp, stacks 04WK "inverse-image Hom two-cell computation"]
theorem toMor₂ {F G : I.target ⟶ T} (eta : F ⟶ G) :
    StackOver.Hom.toMor₂ ((homFunctor I T).map eta) =
      FiberedCategoryOver.Pushforward.Hom.map (hX := I.sourceChoice) u
        (I.comparisonHom ◁ StackOver.Hom.toMor₂ eta) := sorry

/-- The based natural transformation underlying the morphism action is the canonical pullback
comparison transformation applied to the left-whiskered ambient cell. -/
@[simp, stacks 04WK "inverse-image Hom based two-cell computation"]
theorem toBasedNatTrans {F G : I.target ⟶ T} (eta : F ⟶ G) :
    StackOver.Hom₂.toBasedNatTrans ((homFunctor I T).map eta) =
      FiberedCategoryOver.Pushforward.Precompose.map (hX := I.sourceChoice) u
        (FiberedCategoryOver.toBasedNatTrans
          (I.comparisonHom ◁ StackOver.Hom.toMor₂ eta)) := sorry

/-- The total natural transformation underlying the morphism action is the total transformation
of the canonical based pullback comparison. -/
@[simp, stacks 04WK "inverse-image Hom natural transformation computation"]
theorem toNatTrans {F G : I.target ⟶ T} (eta : F ⟶ G) :
    StackOver.Hom₂.toNatTrans ((homFunctor I T).map eta) =
      (FiberedCategoryOver.Pushforward.Precompose.map (hX := I.sourceChoice) u
        (FiberedCategoryOver.toBasedNatTrans
          (I.comparisonHom ◁ StackOver.Hom.toMor₂ eta))).toNatTrans := sorry

/-- The component at `x` of the morphism action is the canonical categorical-pullback component
of the left-whiskered ambient cell. -/
@[simp, stacks 04WK "inverse-image Hom component computation"]
theorem app {F G : I.target ⟶ T} (eta : F ⟶ G) (x : S.total) :
    (StackOver.Hom₂.toNatTrans ((homFunctor I T).map eta)).app x =
      FiberedCategoryOver.Pushforward.Precompose.mapApp (hX := I.sourceChoice) u
        (FiberedCategoryOver.toBasedNatTrans
          (I.comparisonHom ◁ StackOver.Hom.toMor₂ eta)) x := sorry

end homFunctor.map

end StackOver.InverseImage

end CategoryTheory
