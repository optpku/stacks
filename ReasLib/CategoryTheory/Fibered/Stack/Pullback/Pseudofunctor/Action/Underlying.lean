/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Pullback.Pseudofunctor.Action.Construction

/-!
# Underlying action computations for fixed-base pullback on stacks

This leaf relates the bundled stack action to the neutral action on based functors and total
categories.
-/

@[expose] public section

noncomputable section

universe uC uD uS vC vD vS

namespace CategoryTheory

open Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

namespace StackOver.Pullback

variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)
variable [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] [u.IsContinuous J K]

/-- The object action of the stack pullback pseudofunctor is `StackOver.pullback`. -/
@[simp, stacks 04WC "pullback pseudofunctor object"]
theorem pseudofunctor.obj (T : StackOver.{uD, vD, uS, vS} K) :
    (pseudofunctor J K u).obj T = StackOver.pullback u T := rfl

/-- The `1`-cell action of the stack pullback pseudofunctor is the named pullback map. -/
@[simp, stacks 04WC "pullback pseudofunctor morphism"]
theorem pseudofunctor.map
    {X Y : StackOver.{uD, vD, uS, vS} K} (F : X ⟶ Y) :
    (pseudofunctor J K u).map F = map (J := J) (K := K) u F := rfl

/-- The `2`-cell action of the stack pullback pseudofunctor is the named pullback
transformation. -/
@[simp, stacks 04WC "pullback pseudofunctor 2-morphism"]
theorem pseudofunctor.map₂
    {X Y : StackOver.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (pseudofunctor J K u).map₂ eta =
      map₂ (J := J) (K := K) u eta := rfl

/-- Forgetting the stack condition from a pulled-back `1`-cell recovers the neutral canonical
pullback map. -/
@[simp, stacks 04WC "pullback morphism underlying map"]
theorem map.hom
    {X Y : StackOver.{uD, vD, uS, vS} K} (F : X ⟶ Y) :
    (map (J := J) (K := K) u F).hom =
      FiberedCategoryOver.Pullback.mapCanonical u F.hom := rfl

/-- Forgetting the stack condition from a pulled-back `2`-cell recovers the neutral canonical
pullback transformation. -/
@[simp, stacks 04WC "pullback 2-morphism underlying map"]
theorem map₂.hom
    {X Y : StackOver.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (map₂ (J := J) (K := K) u eta).hom =
      FiberedCategoryOver.Pullback.map₂ u eta.hom := rfl

/-- The based functor underlying stack pullback on a `1`-cell is the neutral based pullback map. -/
@[simp, stacks 04WC "pullback morphism based computation"]
theorem map.toBasedFunctor
    {X Y : StackOver.{uD, vD, uS, vS} K} (F : X ⟶ Y) :
    StackOver.Hom.toBasedFunctor (map (J := J) (K := K) u F) =
      FiberedCategoryOver.Pullback.basedMap u F.hom := rfl

/-- The total functor underlying stack pullback on a `1`-cell is the categorical-pullback
comparison. -/
@[simp, stacks 04WC "pullback morphism total computation"]
theorem map.toFunctor
    {X Y : StackOver.{uD, vD, uS, vS} K} (F : X ⟶ Y) :
    StackOver.Hom.toFunctor (map (J := J) (K := K) u F) =
      FiberedCategoryOver.Pullback.totalMap u F.hom := rfl

/-- The based natural transformation underlying stack pullback on a `2`-cell is the neutral
based pullback transformation. -/
@[simp, stacks 04WC "pullback 2-morphism based computation"]
theorem map₂.toBasedNatTrans
    {X Y : StackOver.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    StackOver.Hom₂.toBasedNatTrans (map₂ (J := J) (K := K) u eta) =
      FiberedCategoryOver.Pullback.basedMap₂ u eta.hom := rfl

/-- The total natural transformation underlying stack pullback on a `2`-cell is the neutral
total pullback transformation. -/
@[simp, stacks 04WC "pullback 2-morphism total computation"]
theorem map₂.toNatTrans
    {X Y : StackOver.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    StackOver.Hom₂.toNatTrans (map₂ (J := J) (K := K) u eta) =
      FiberedCategoryOver.Pullback.totalMap₂ u eta.hom := rfl

end StackOver.Pullback

end CategoryTheory
