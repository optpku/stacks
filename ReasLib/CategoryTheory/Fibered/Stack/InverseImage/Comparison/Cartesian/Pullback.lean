/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Pushforward.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Heterogeneous pullback comparison for an inverse-image stack

The canonical comparison is a `CartesianBasedFunctor`, so its source and target total categories
may live in independent universes.  Bundling it as a morphism of `StackOver` objects is a later
fixed-universe companion.
-/

@[expose] public section

universe uC uD vC vD uS vS uT vT

namespace CategoryTheory

open Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace StackOver.InverseImage.Cartesian

variable {u : C ⥤ D} {S : StackOver.{uC, vC, uS, vS} J}
variable (I : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT, vT} K u S)

/-- Lemma 8.12.12 (1) (tag 04WS): specialize the neutral pushforward-pullback comparison to the
explicit source choice and stackification comparison of an inverse-image stack. -/
@[stacks 04WS "heterogeneous inverse-image pullback comparison"]
noncomputable abbrev pullbackComparison
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    CartesianBasedFunctor S.p
      (FiberedCategoryOver.pullback u I.target.toFiberedCategoryOver).p :=
  CartesianBasedFunctor.PushforwardHom.pullbackComparison
    I.comparison

/-- Forgetting the heterogeneous pullback comparison to a based functor recovers the neutral
pushforward-pullback Hom construction applied to `I.comparison`. -/
@[simp, stacks 04WS "heterogeneous inverse-image pullback based computation"]
theorem pullbackComparison.toBasedFunctor
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    (pullbackComparison I).toBasedFunctor =
      FiberedCategoryOver.Pushforward.Precompose.obj
        (hX := I.sourceChoice) u I.comparison.toBasedFunctor := sorry

/-- The total functor of the heterogeneous pullback comparison is the neutral comparison functor
obtained by precomposing with the pushforward unit. -/
@[simp, stacks 04WS "heterogeneous inverse-image pullback total computation"]
theorem pullbackComparison.toFunctor
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    (pullbackComparison I).toFunctor =
      FiberedCategoryOver.Pushforward.Precompose.functor
        (hX := I.sourceChoice) u I.comparison.toBasedFunctor := sorry

/-- Lemma 8.12.12 (1) (tag 04WS): under the invariant finite-limit hypotheses, the
heterogeneous pullback comparison is an equivalence over the base. -/
@[stacks 04WS "heterogeneous pullback comparison equivalence"]
instance pullbackComparison.isEquivalence
    [HasFiniteLimits C] [PreservesFiniteLimits u]
    [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful] :
    (pullbackComparison I).toBasedFunctor.IsEquivalence := sorry

/- Axiom audit: `pullbackComparison` applies the neutral cartesian Hom construction to the
explicit fields `I.sourceChoice` and `I.comparison`; it makes no additional choice. -/

end StackOver.InverseImage.Cartesian

end CategoryTheory
