/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Map.TwoCell.CartesianBasedFunctor.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushforward two-cells of fibred categories

This file converts the universe-polymorphic cartesian pushforward transformation into a `2`-cell
between fixed-universe fibred categories and exposes its forgetful computations.
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

/-- Pushforward of a `2`-cell between morphisms of fibred categories, obtained by converting
the universe-polymorphic cartesian pushforward `2`-cell. -/
@[stacks 04WI "bundled fibred pushforward two-cell"]
noncomputable def map₂
    {F G : X ⟶ Y}
    (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (hF : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor F))
    (hG : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor G))
    (eta : F ⟶ G) : map u F hX hY hF ⟶ map u G hX hY hG :=
  (FiberedCategoryOver.CartesianHom.toHom
    (FiberedCategoryOver.pushforward u X hX)
    (FiberedCategoryOver.pushforward u Y hY)).map
      (CartesianBasedFunctor.Pushforward.map₂ u
        hX.raw hY.raw hF hG
        ((FiberedCategoryOver.CartesianHom.fromHom X Y).map eta))

/-- The bundled pushforward `2`-cell determined by a fixed-owner inversion choice. This keeps the
endpoint and morphism proof data together, while the explicit `map₂` remains available when a
consumer must pin each proof term separately. -/
@[stacks 04WI "bundled fibred pushforward two-cell from inversion choice"]
noncomputable def map₂.ofInversionChoice
    {F G : X ⟶ Y} (h : InversionChoice u X Y) (eta : F ⟶ G) :
    map.ofInversionChoice u F h ⟶ map.ofInversionChoice u G h :=
  map₂ u h.source h.target (h.inverts F) (h.inverts G) eta

/-- The bundled inversion-choice pushforward `2`-cell preserves identities. -/
@[simp, stacks 04WI "bundled fibred pushforward two-cell identity"]
theorem map₂.ofInversionChoice.id
    (h : InversionChoice u X Y) (F : X ⟶ Y) :
    map₂.ofInversionChoice u h (𝟙 F) =
      𝟙 (map.ofInversionChoice u F h) := sorry

/-- The bundled inversion-choice pushforward `2`-cell preserves vertical composition. -/
@[simp, stacks 04WI "bundled fibred pushforward two-cell composition"]
theorem map₂.ofInversionChoice.comp
    (h : InversionChoice u X Y) {F G H : X ⟶ Y}
    (eta : F ⟶ G) (theta : G ⟶ H) :
    map₂.ofInversionChoice u h (eta ≫ theta) =
      map₂.ofInversionChoice u h eta ≫ map₂.ofInversionChoice u h theta := sorry

/-- Forgetting a fixed-owner pushforward `2`-cell recovers the universe-polymorphic cartesian
pushforward `2`-cell. -/
@[simp, stacks 04WI "bundled pushforward two-cell cartesian form"]
theorem map₂.toCartesianBasedFunctor
    {F G : X ⟶ Y}
    (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (hF : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor F))
    (hG : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor G))
    (eta : F ⟶ G) :
    (FiberedCategoryOver.CartesianHom.fromHom
      (FiberedCategoryOver.pushforward u X hX)
      (FiberedCategoryOver.pushforward u Y hY)).map (map₂ u hX hY hF hG eta) =
        CartesianBasedFunctor.Pushforward.map₂ u
          hX.raw hY.raw hF hG
          ((FiberedCategoryOver.CartesianHom.fromHom X Y).map eta) := sorry

/-- The total natural transformation of a fixed-owner pushforward `2`-cell is the explicitly
certified raw localized extension. -/
@[simp, stacks 04WI "bundled pushforward two-cell total form"]
theorem map₂.toNatTrans
    {F G : X ⟶ Y}
    (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (hF : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor F))
    (hG : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor G))
    (eta : F ⟶ G) :
    FiberedCategoryOver.toNatTrans (map₂ u hX hY hF hG eta) =
      Functor.Pushforward.map₂ u hF hG
        ((FiberedCategoryOver.CartesianHom.fromHom X Y).map eta) := sorry

/-- Two pushforward `2`-cells agree when their total-category components agree. -/
@[stacks 04WI "bundled pushforward two-cell extensionality"]
theorem map₂.ext
    {F G : X ⟶ Y}
    (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (hF : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor F))
    (hG : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor G))
    {eta theta : F ⟶ G}
    (h : ∀ A : (FiberedCategoryOver.pushforward u X hX).total,
      (FiberedCategoryOver.toNatTrans (map₂ u hX hY hF hG eta)).app A =
        (FiberedCategoryOver.toNatTrans (map₂ u hX hY hF hG theta)).app A) :
    map₂ u hX hY hF hG eta = map₂ u hX hY hF hG theta := sorry

end CategoryTheory.FiberedCategoryOver.Pushforward

-- Data audit: fixed-universe packaging reuses the universe-polymorphic cartesian owner.
