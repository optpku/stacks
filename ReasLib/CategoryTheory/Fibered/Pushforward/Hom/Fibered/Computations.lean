/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Hom.Fibered.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for the bundled pushforward-pullback Hom functor

This file exposes the based, total-category, componentwise, and functorial computation API for
the bundled Hom construction.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Limits
open scoped Bicategory

namespace FiberedCategoryOver.Pushforward

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

namespace Hom

/-- Forgetting a bundled precomposition object recovers the underlying based comparison
functor. -/
@[simp, stacks 04WI "bundled Hom object based computation"]
theorem obj.toBasedFunctor
    {X : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    (G : FiberedCategoryOver.pushforward u X hX ⟶ Y) :
    FiberedCategoryOver.toBasedFunctor (obj u G) =
      Precompose.obj u (FiberedCategoryOver.toBasedFunctor G) := sorry

/-- The total functor of a bundled precomposition object is the categorical-pullback comparison
functor. -/
@[simp, stacks 04WI "bundled Hom object total computation"]
theorem obj.toFunctor
    {X : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    (G : FiberedCategoryOver.pushforward u X hX ⟶ Y) :
    FiberedCategoryOver.toFunctor (obj u G) =
      Precompose.functor u (FiberedCategoryOver.toBasedFunctor G) := sorry

/-- Forgetting a bundled precomposition `2`-cell recovers the underlying based comparison
transformation. -/
@[simp, stacks 04WI "bundled Hom map based computation"]
theorem map.toBasedNatTrans
    {X : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    {G H : FiberedCategoryOver.pushforward u X hX ⟶ Y} (τ : G ⟶ H) :
    FiberedCategoryOver.toBasedNatTrans (map u τ) =
      Precompose.map u (FiberedCategoryOver.toBasedNatTrans τ) := sorry

/-- The component of a bundled precomposition `2`-cell is the corresponding morphism in the
categorical pullback. -/
@[simp, stacks 04WI "bundled Hom map component computation"]
theorem map.app
    {X : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    {G H : FiberedCategoryOver.pushforward u X hX ⟶ Y}
    (τ : G ⟶ H) (x : X.total) :
    (FiberedCategoryOver.toNatTrans (map u τ)).app x =
      Precompose.mapApp u (FiberedCategoryOver.toBasedNatTrans τ) x := sorry

/-- The map on fibred-category transformations induced by unit precomposition preserves
identities. -/
@[simp, stacks 04WI "bundled Hom map identity"]
theorem map.id
    {X : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    (G : FiberedCategoryOver.pushforward u X hX ⟶ Y) :
    map u (𝟙 G) = 𝟙 (obj u G) := sorry

/-- The map on fibred-category transformations induced by unit precomposition preserves
vertical composition. -/
@[simp, stacks 04WI "bundled Hom map composition"]
theorem map.comp
    {X : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    {G H K : FiberedCategoryOver.pushforward u X hX ⟶ Y}
    (τ : G ⟶ H) (σ : H ⟶ K) :
    map u (τ ≫ σ) = map u τ ≫ map u σ := sorry

end Hom

namespace homFunctor

/-- Objectwise computation for the pushforward-pullback Hom functor. -/
@[simp, stacks 04WI "pushforward-pullback Hom object computation"]
theorem obj
    {X : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    (G : FiberedCategoryOver.pushforward u X hX ⟶ Y) :
    (homFunctor u hX Y).obj G = Hom.obj u G := sorry

/-- Morphismwise computation for the pushforward-pullback Hom functor. -/
@[simp, stacks 04WI "pushforward-pullback Hom map computation"]
theorem map
    {X : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    {G H : FiberedCategoryOver.pushforward u X hX ⟶ Y} (τ : G ⟶ H) :
    (homFunctor u hX Y).map τ = Hom.map u τ := sorry

end homFunctor

end FiberedCategoryOver.Pushforward

end CategoryTheory
