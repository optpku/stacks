/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Pseudofunctor.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for the pushforward pseudofunctor

This leaf exposes the object, `1`-cell, `2`-cell, comparison, and hom-functor actions of the
pushforward pseudofunctor.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Bicategory Limits
open scoped Bicategory

namespace FiberedCategoryOver.Pushforward

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- The object action of the pushforward pseudofunctor is the bundled pushforward selected by
the coherent choice. -/
@[simp, stacks 04WI "pushforward pseudofunctor object computation"]
theorem pseudofunctor.obj
    (h : CoherentInversionChoice u)
    (X : FiberedCategoryOver.{uC, vC, w₀, w₁} C) :
    (pseudofunctor u h).obj X = FiberedCategoryOver.pushforward u X (h.obj X) := sorry

/-- The `1`-cell action of the pushforward pseudofunctor uses the supplied inversion proof. -/
@[simp, stacks 04WI "pushforward pseudofunctor morphism computation"]
theorem pseudofunctor.map
    (h : CoherentInversionChoice u)
    {X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C} (F : X ⟶ Y) :
    (pseudofunctor u h).map F =
      map u F (h.obj X) (h.obj Y) (h.inverts F) := sorry

/-- The `2`-cell action of the pushforward pseudofunctor is the canonical localized natural
transformation. -/
@[simp, stacks 04WI "pushforward pseudofunctor two-cell computation"]
theorem pseudofunctor.map₂
    (h : CoherentInversionChoice u)
    {X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (pseudofunctor u h).map₂ eta =
      map₂ u (h.obj X) (h.obj Y) (h.inverts F) (h.inverts G) eta := sorry

/-- The identity comparison of the pushforward pseudofunctor is the explicit comparison supplied
by the coherent choice. -/
@[simp, stacks 04WI "pushforward pseudofunctor identity comparison"]
theorem pseudofunctor.mapId
    (h : CoherentInversionChoice u)
    (X : FiberedCategoryOver.{uC, vC, w₀, w₁} C) :
    (pseudofunctor u h).mapId X = h.mapId X := sorry

/-- The composition comparison of the pushforward pseudofunctor is the explicit comparison
supplied by the coherent choice. -/
@[simp, stacks 04WI "pushforward pseudofunctor composition comparison"]
theorem pseudofunctor.mapComp
    (h : CoherentInversionChoice u)
    {X Y Z : FiberedCategoryOver.{uC, vC, w₀, w₁} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    (pseudofunctor u h).mapComp F G = h.mapComp F G := sorry

/-- On each hom category, the pushforward pseudofunctor is the existing computational hom
functor. -/
@[simp, stacks 04WI "pushforward pseudofunctor Hom functor computation"]
theorem pseudofunctor.mapFunctor
    (h : CoherentInversionChoice u)
    (X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C) :
    (pseudofunctor u h).mapFunctor X Y = mapFunctor u (h.hom X Y) := sorry

/-- The object action of the pushforward pseudofunctor's Hom functor uses the supplied inversion
proof. -/
@[simp, stacks 04WI "pushforward pseudofunctor Hom object computation"]
theorem pseudofunctor.mapFunctor.obj
    (h : CoherentInversionChoice u)
    {X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C} (F : X ⟶ Y) :
    ((pseudofunctor u h).mapFunctor X Y).obj F =
      FiberedCategoryOver.Pushforward.map u F
        (h.obj X) (h.obj Y) (h.inverts F) := sorry

/-- The morphism action of the pushforward pseudofunctor's hom functor is pushforward on
`2`-cells. -/
@[simp, stacks 04WI "pushforward pseudofunctor Hom map computation"]
theorem pseudofunctor.mapFunctor.map
    (h : CoherentInversionChoice u)
    {X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    ((pseudofunctor u h).mapFunctor X Y).map eta =
      _root_.CategoryTheory.FiberedCategoryOver.Pushforward.map₂ u
        (h.obj X) (h.obj Y) (h.inverts F) (h.inverts G) eta := sorry

end FiberedCategoryOver.Pushforward

end CategoryTheory

-- Data audit: `h` supplies the inversion family and explicit identity/composition comparisons;
-- unfinished theorems occur only in bicategorical coherence fields.
