/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Hom.Cartesian
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushforward Hom functors after stackification

Precomposition by a stackification and precomposition by the pushforward unit are independently
equivalences on cartesian Hom categories.  This leaf owns their universe-polymorphic composite;
inverse-image stacks use it as their neutral Hom-equivalence layer.
-/

@[expose] public section

universe uC uD vC vD uX vX uY vY uT vT

namespace CategoryTheory

open Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {K : GrothendieckTopology D}

namespace CartesianBasedFunctor.PushforwardHom

/-- Lemma 8.12.10 (tag 04WK), functor owner: compose precomposition by a heterogeneous
stackification with the cartesian pushforward-pullback Hom functor. The three total categories
may live in independent universes. -/
@[stacks 04WK "pushforward Hom functor after stackification"]
noncomputable def functor
    {u : C ⥤ D} [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : FiberedCategoryOver.Pushforward.ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (i : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p)
    (T : FiberedCategoryOver.{uD, vD, uT, vT} D) :
    CartesianBasedFunctor Y.p T.p ⥤
      CartesianBasedFunctor X.p (FiberedCategoryOver.pullback u T).p :=
  CartesianBasedFunctor.precomp T.p i ⋙
    FiberedCategoryOver.Pushforward.CartesianHom.functor u hX T

namespace functor

/-- The object action first precomposes with the stackification map and then applies the
pushforward-pullback Hom construction. -/
@[simp, stacks 04WK "pushforward Hom object after stackification"]
theorem obj
    {u : C ⥤ D} [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : FiberedCategoryOver.Pushforward.ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (i : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p)
    (T : FiberedCategoryOver.{uD, vD, uT, vT} D)
    (G : CartesianBasedFunctor Y.p T.p) :
    (PushforwardHom.functor i T).obj G =
      FiberedCategoryOver.Pushforward.CartesianHom.obj (hX := hX) u (i.comp G) := sorry

/-- The morphism action first whisks with the stackification map and then applies the
pushforward-pullback Hom construction. -/
@[simp, stacks 04WK "pushforward Hom map after stackification"]
theorem map
    {u : C ⥤ D} [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : FiberedCategoryOver.Pushforward.ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (i : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p)
    (T : FiberedCategoryOver.{uD, vD, uT, vT} D)
    {G H : CartesianBasedFunctor Y.p T.p} (eta : G ⟶ H) :
    (PushforwardHom.functor i T).map eta =
      FiberedCategoryOver.Pushforward.CartesianHom.map (hX := hX) u
        ((CartesianBasedFunctor.precomp T.p i).map eta) := sorry

/-- The composite pushforward Hom functor is an equivalence when its first map is a
stackification and the final target is a stack. -/
@[stacks 04WK "heterogeneous inverse-image/direct-image Hom equivalence"]
theorem isEquivalence
    {u : C ⥤ D} [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : FiberedCategoryOver.Pushforward.ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (i : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p)
    (hi : CartesianBasedFunctor.IsStackification K i)
    (T : FiberedCategoryOver.{uD, vD, uT, vT} D) [IsStack.OnSite K T.p] :
    (PushforwardHom.functor i T).IsEquivalence := sorry

end functor

end CartesianBasedFunctor.PushforwardHom

end CategoryTheory

/- Axiom audit: `PushforwardHom.functor` is a composition of the two canonical Hom functors;
it introduces no chosen inverse or comparison data. -/
