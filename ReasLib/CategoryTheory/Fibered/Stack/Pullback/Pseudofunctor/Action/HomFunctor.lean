module

public import ReasLib.CategoryTheory.Fibered.Stack.Pullback.Pseudofunctor.Action.Construction

/-!
# Hom-functor computations for fixed-base pullback on stacks

This leaf identifies both actions of the hom functor with the direct `map` and `map₂` owners.
-/

@[expose] public section

noncomputable section

universe uC uD uS vC vD vS

namespace CategoryTheory.StackOver.Pullback

open CategoryTheory Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)
variable [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] [u.IsContinuous J K]

/-- The object action of the stack pullback hom functor has the canonical ambient representative. -/
@[simp, stacks 04WC "pullback Hom object underlying computation"]
theorem mapFunctor.obj.hom
    {X Y : StackOver.{uD, vD, uS, vS} K} (F : X ⟶ Y) :
    ((mapFunctor (J := J) (K := K) u X Y).obj F).hom =
      FiberedCategoryOver.Pullback.mapCanonical u F.hom := sorry

/-- The morphism action of the stack pullback hom functor has the canonical ambient
representative. -/
@[simp, stacks 04WC "pullback Hom morphism underlying computation"]
theorem mapFunctor.map.hom
    {X Y : StackOver.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    ((mapFunctor (J := J) (K := K) u X Y).map eta).hom =
      FiberedCategoryOver.Pullback.map₂ u eta.hom := sorry

/-- The object action of the stack pullback hom functor is `map`. -/
@[simp, stacks 04WC "pullback Hom object computation"]
theorem mapFunctor.obj
    {X Y : StackOver.{uD, vD, uS, vS} K} (F : X ⟶ Y) :
    (mapFunctor (J := J) (K := K) u X Y).obj F =
      map (J := J) (K := K) u F := sorry

/-- The morphism action of the stack pullback hom functor is `map₂`. -/
@[simp, stacks 04WC "pullback Hom morphism computation"]
theorem mapFunctor.map
    {X Y : StackOver.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (mapFunctor (J := J) (K := K) u X Y).map eta =
      map₂ (J := J) (K := K) u eta := sorry

end CategoryTheory.StackOver.Pullback
