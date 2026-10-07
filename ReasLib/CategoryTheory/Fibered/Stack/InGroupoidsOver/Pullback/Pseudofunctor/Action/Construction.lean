module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Pullback.Pseudofunctor.Action.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Pullback.Pseudofunctor.Construction

/-!
# Direct action of fixed-base pullback on stacks in groupoids

This file owns the application-facing `1`-cell, `2`-cell, and hom-functor actions of pullback on
stacks in groupoids.
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

/-- Pullback of a `1`-morphism between stacks in groupoids. -/
@[stacks 04WD "pullback action on groupoid-stack morphisms"]
noncomputable def map
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K} (F : X ⟶ Y) :
    StackOver.Groupoids.pullback (J := J) (K := K) u X ⟶
      StackOver.Groupoids.pullback (J := J) (K := K) u Y :=
  (pseudofunctor J K u).map F

/-- Pullback of a `2`-morphism between morphisms of stacks in groupoids. -/
@[stacks 04WD "pullback action on groupoid-stack 2-morphisms"]
noncomputable def map₂
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    map (J := J) (K := K) u F ⟶ map (J := J) (K := K) u G :=
  (pseudofunctor J K u).map₂ eta

/-- For fixed `u`, pullback acts functorially on each hom category of stacks in groupoids. -/
@[stacks 04WD "pullback Hom functor on groupoid stacks"]
noncomputable def mapFunctor
    (X Y : StackOver.Groupoids.{uD, vD, uS, vS} K) :
    (X ⟶ Y) ⥤
      (StackOver.Groupoids.pullback (J := J) (K := K) u X ⟶
        StackOver.Groupoids.pullback (J := J) (K := K) u Y) :=
  (pseudofunctor J K u).mapFunctor X Y

end CategoryTheory.StackOver.Groupoids.Pullback
