/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.Cartesian.Pullback
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback comparison for an inverse-image stack

For a chosen inverse-image stack `I` of `S` along a functor of sites `u`, the
inverse-image/direct-image Hom functor sends `𝟙 I.target` to the canonical
comparison `S ⟶ StackOver.pullback u I.target`.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Limits
open scoped Bicategory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace StackOver.InverseImage

variable {u : C ⥤ D}
variable {S : StackOver.{uC, vC,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
variable (I : StackOver.InverseImage.{uC, uD, vC, vD,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD)))),
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} K u S)

/-- The fixed-universe companion of `Cartesian.pullbackComparison`, bundled as a morphism from a
stack `S` to the pullback of its chosen inverse-image target. -/
@[stacks 04WS "fixed-universe inverse-image pullback comparison"]
noncomputable def pullbackComparison
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [u.IsContinuous J K] :
    S ⟶ StackOver.pullback (J := J) (K := K) u I.target :=
  StackOver.Hom.lift
    ((FiberedCategoryOver.CartesianHom.toHom S.toFiberedCategoryOver
      (StackOver.pullback (J := J) (K := K) u I.target).toFiberedCategoryOver).obj
        (Cartesian.pullbackComparison I))

/-- Forgetting the fixed-universe pullback comparison recovers the canonical heterogeneous
cartesian comparison. -/
@[simp, stacks 04WS "fixed inverse-image pullback comparison computation"]
theorem pullbackComparison.toCartesianBasedFunctor
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [u.IsContinuous J K] :
    FiberedCategoryOver.toCartesianBasedFunctor
        (StackOver.Hom.toMor (pullbackComparison I)) =
      Cartesian.pullbackComparison I := sorry

/-- The ambient pullback comparison is canonically isomorphic to the Hom image of the
stackification comparison itself. Its component is obtained by mapping the bicategorical right
unitor, so no equality proof is converted into morphism data. -/
@[stacks 04WS "fixed inverse-image pullback comparison isomorphism"]
noncomputable def pullbackComparison.toMorIso
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [u.IsContinuous J K] :
    StackOver.Hom.toMor (pullbackComparison I) ≅
      FiberedCategoryOver.Pushforward.Hom.obj (hX := I.sourceChoice) u I.comparisonHom :=
  (FiberedCategoryOver.Pushforward.homFunctor u I.sourceChoice
    I.target.toFiberedCategoryOver).mapIso (ρ_ I.comparisonHom)

/-- Lemma 8.12.12 (1) (tag 04WS): under the hypotheses of Sites, Lemma 7.21.8, the canonical
comparison from `S` to `StackOver.pullback u I.target` is an equivalence of stacks. The source's
terminal-object and fibre-product assumptions are represented invariantly by finite-limit
existence and preservation. -/
@[stacks 04WS]
instance pullbackComparison.isEquivalence
    [HasFiniteLimits C] [PreservesFiniteLimits u]
    [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful] :
    StackOver.Hom.IsEquivalence (pullbackComparison I) := sorry

end StackOver.InverseImage

end CategoryTheory
