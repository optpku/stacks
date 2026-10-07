module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Pullback.Pseudofunctor.Action.Construction

/-!
# Hom-functor computations for fixed-base pullback on stacks in groupoids

This leaf identifies both hom-functor actions with the direct `map` and `map₂` owners.
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

/-- The object action of the stack-in-groupoids pullback hom functor is `map`. -/
@[simp, stacks 04WD "groupoid pullback Hom object computation"]
theorem mapFunctor.obj
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K} (F : X ⟶ Y) :
    (mapFunctor (J := J) (K := K) u X Y).obj F =
      map (J := J) (K := K) u F := sorry

/-- The morphism action of the stack-in-groupoids pullback hom functor is `map₂`. -/
@[simp, stacks 04WD "groupoid pullback Hom morphism computation"]
theorem mapFunctor.map
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (mapFunctor (J := J) (K := K) u X Y).map eta =
      map₂ (J := J) (K := K) u eta := sorry

end CategoryTheory.StackOver.Groupoids.Pullback
