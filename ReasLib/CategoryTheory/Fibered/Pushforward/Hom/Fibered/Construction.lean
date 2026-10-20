/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Hom.Cartesian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bundled pushforward-pullback Hom construction

This file transports the universe-polymorphic cartesian Hom comparison to morphisms of bundled
fibered categories. It owns the object action, `2`-cell action, and resulting Hom functor; their
computation, naturality, and equivalence APIs are in focused sibling modules.
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

/-- Lemma 8.12.8 (tag 04WI): the image of a fibred-category morphism under precomposition
with the pushforward unit. -/
@[stacks 04WI "bundled pushforward Hom object"]
noncomputable def obj
    {X : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    (G : FiberedCategoryOver.pushforward u X hX ⟶ Y) :
    X ⟶ FiberedCategoryOver.pullback u Y :=
  (FiberedCategoryOver.CartesianHom.toHom X
    (FiberedCategoryOver.pullback u Y)).obj
      (CartesianHom.obj u
        ((FiberedCategoryOver.CartesianHom.fromHom
          (FiberedCategoryOver.pushforward u X hX) Y).obj G))

/-- Lemma 8.12.8 (tag 04WI): the image of a vertical transformation under precomposition with
the pushforward unit. -/
@[stacks 04WI "bundled pushforward Hom map"]
noncomputable def map
    {X : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    {G H : FiberedCategoryOver.pushforward u X hX ⟶ Y} (τ : G ⟶ H) :
    obj u G ⟶ obj u H :=
  (FiberedCategoryOver.CartesianHom.toHom X
    (FiberedCategoryOver.pullback u Y)).map
      (CartesianHom.map u
        ((FiberedCategoryOver.CartesianHom.fromHom
          (FiberedCategoryOver.pushforward u X hX) Y).map τ))

end Hom

/-- Lemma 8.12.8 (tag 04WI): the functor associated to an explicit projection choice,
`Hom(u ₚ X, Y) ⥤ Hom(X, u ᵖ Y)` for fibred categories, induced by precomposition with the
pushforward unit. -/
@[stacks 04WI "bundled pushforward-pullback Hom functor"]
noncomputable def homFunctor
    {X : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    (hX : ProjectionChoice u X)
    (Y : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D) :
    (FiberedCategoryOver.pushforward u X hX ⟶ Y) ⥤
      (X ⟶ FiberedCategoryOver.pullback u Y) :=
  FiberedCategoryOver.CartesianHom.fromHom
      (FiberedCategoryOver.pushforward u X hX) Y ⋙
    CartesianHom.functor u hX Y ⋙
      FiberedCategoryOver.CartesianHom.toHom X
        (FiberedCategoryOver.pullback u Y)

end FiberedCategoryOver.Pushforward

end CategoryTheory
