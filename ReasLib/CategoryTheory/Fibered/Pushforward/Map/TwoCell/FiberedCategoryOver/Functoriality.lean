/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Map.TwoCell.FiberedCategoryOver.Construction
public import ReasLib.CategoryTheory.Fibered.Pushforward.Map.TwoCell.CartesianBasedFunctor.Functoriality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of pushforward two-cells of fibred categories

This file owns the identity and composition laws and the Hom functor for bundled pushforward.
-/

@[expose] public section

universe uC uD uS vC vD vS

namespace CategoryTheory.FiberedCategoryOver.Pushforward

open Limits
open scoped Bicategory Functor

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {X Y : FiberedCategoryOver.{uC, vC, uS, vS} C}
variable (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- Bundled pushforward preserves identity `2`-cells. -/
@[simp, stacks 04WI "bundled pushforward two-cell identity"]
theorem map₂.id (F : X ⟶ Y)
    (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (hF : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor F)) :
    map₂ u hX hY hF hF (𝟙 F) = 𝟙 (map u F hX hY hF) := sorry

/-- Bundled pushforward preserves vertical composition of `2`-cells. -/
@[simp, stacks 04WI "bundled pushforward two-cell composition"]
theorem map₂.comp
    {F G H : X ⟶ Y}
    (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (hF : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor F))
    (hG : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor G))
    (hH : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor H))
    (eta : F ⟶ G) (theta : G ⟶ H) :
    map₂ u hX hY hF hH (eta ≫ theta) =
      map₂ u hX hY hF hG eta ≫ map₂ u hX hY hG hH theta := sorry

/-- Pushforward acts functorially on each hom category of fibred categories. -/
@[stacks 04WI "bundled pushforward Hom functor"]
noncomputable def mapFunctor {X Y : FiberedCategoryOver.{uC, vC, uS, vS} C}
    (h : InversionChoice u X Y) :
    (X ⟶ Y) ⥤
      (FiberedCategoryOver.pushforward u X h.source ⟶
        FiberedCategoryOver.pushforward u Y h.target) where
  obj F := map.ofInversionChoice u F h
  map {_ _} eta := map₂.ofInversionChoice u h eta
  map_id F := map₂.ofInversionChoice.id u h F
  map_comp eta theta := map₂.ofInversionChoice.comp u h eta theta

/-- The object action of the pushforward Hom functor uses the supplied inversion proof. -/
@[simp, stacks 04WI "bundled pushforward Hom functor object"]
theorem mapFunctor.obj (h : InversionChoice u X Y) (F : X ⟶ Y) :
    (mapFunctor u h).obj F =
      map u F h.source h.target (h.inverts F) := sorry

/-- The morphism action of the pushforward hom functor is pushforward on `2`-cells. -/
@[simp, stacks 04WI "bundled pushforward Hom functor map"]
theorem mapFunctor.map (h : InversionChoice u X Y)
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (mapFunctor u h).map eta =
      map₂.ofInversionChoice u h eta := sorry

end CategoryTheory.FiberedCategoryOver.Pushforward

-- Data audit: object and morphism data use the supplied fixed-owner choices directly; only the
-- functor-law fields depend on the proposition-valued `map₂.id` and `map₂.comp` theorems.
