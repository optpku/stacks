/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Pullback.Pseudofunctor.Construction

/-!
# Direct action of fixed-base pullback on stacks

This file owns the application-facing `1`-cell, `2`-cell, and hom-functor actions of fixed-base
pullback on stacks.
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

/-/ Pullback of a `1`-morphism between stacks along the fixed morphism of sites `u`. -/
@[stacks 04WC "pullback action on stack morphisms"]
noncomputable def map
    {X Y : StackOver.{uD, vD, uS, vS} K} (F : X ⟶ Y) :
    StackOver.pullback (J := J) (K := K) u X ⟶
      StackOver.pullback (J := J) (K := K) u Y :=
  (pseudofunctor J K u).map F

/-- Pullback of a `2`-morphism between morphisms of stacks along the fixed morphism of
sites `u`. -/
@[stacks 04WC "pullback action on stack 2-morphisms"]
noncomputable def map₂
    {X Y : StackOver.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    map (J := J) (K := K) u F ⟶ map (J := J) (K := K) u G :=
  (pseudofunctor J K u).map₂ eta

/-- For fixed `u`, pullback acts functorially on each hom category of stacks. -/
@[stacks 04WC "pullback Hom functor on stacks"]
noncomputable def mapFunctor
    (X Y : StackOver.{uD, vD, uS, vS} K) :
    (X ⟶ Y) ⥤
      (StackOver.pullback (J := J) (K := K) u X ⟶
        StackOver.pullback (J := J) (K := K) u Y) :=
  (pseudofunctor J K u).mapFunctor X Y

end CategoryTheory.StackOver.Pullback
