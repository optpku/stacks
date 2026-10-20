/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.CartesianHom
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Cartesian
public import ReasLib.CategoryTheory.Fibered.Pullback.Basic
public import ReasLib.CategoryTheory.Fibered.Pushforward.Unit
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# Precomposition with the pushforward unit

This leaf constructs the pushforward-pullback comparison first for arbitrary based functors.
It owns the categorical-pullback square, the induced based functor, and the action on vertical
natural transformations. The cartesian and bundled restrictions live in later leaves.
-/

@[expose] public section

universe uC uD vC vD uX vX uY vY

namespace CategoryTheory

open Limits
open scoped Functor

namespace FiberedCategoryOver.Pushforward

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

namespace Precompose

/-- Lemma 8.12.8 (tag 04WI): the categorical commutative square induced by precomposing a
based functor from a pushforward with the canonical unit. -/
@[stacks 04WI "pushforward unit pullback square"]
noncomputable def square
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (G : (FiberedCategoryOver.pushforward u X hX).toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    CategoricalPullback.CatCommSqOver u Y.p X.total where
  fst := X.p
  snd := Functor.Pushforward.Unit.functor u X.p ⋙ G.toFunctor
  iso :=
    ((Functor.Pushforward.Unit.over u X.p hX.raw).comp
      G.toOverIso).iso.symm

/-- The total-category functor into the pullback induced by `square`. -/
@[stacks 04WI "pushforward unit pullback comparison functor"]
noncomputable def functor
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (G : (FiberedCategoryOver.pushforward u X hX).toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    X.total ⥤ CategoricalPullback u Y.p :=
  (square u G).comparison

/-- The comparison functor is strictly over the base `C`. -/
@[stacks 04WI "pushforward unit comparison over base"]
theorem functor.compProjection
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (G : (FiberedCategoryOver.pushforward u X hX).toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    functor u G ⋙ (FiberedCategoryOver.pullback u Y).p = X.p := sorry

/-- Lemma 8.12.8 (tag 04WI): the based functor obtained by precomposing a based functor out
of `u ₚ X` with the pushforward unit and then using the categorical-pullback comparison. -/
@[stacks 04WI "pushforward unit Hom object"]
noncomputable def obj
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (G : (FiberedCategoryOver.pushforward u X hX).toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    X.toBasedCategory ⥤ᵇ (FiberedCategoryOver.pullback u Y).toBasedCategory where
  toFunctor := functor u G
  w := functor.compProjection u G

/-- Compatibility of a precomposition map component with the categorical-pullback squares. -/
@[stacks 04WI "pushforward unit Hom component compatibility"]
theorem mapApp.compatibility
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    {G H : (FiberedCategoryOver.pushforward u X hX).toBasedCategory ⥤ᵇ Y.toBasedCategory}
    (τ : G ⟶ H) (x : X.total) :
    u.map (𝟙 (X.p.obj x)) ≫ ((obj u H).obj x).iso.hom =
      ((obj u G).obj x).iso.hom ≫
        Y.p.map (τ.toNatTrans.app ((Functor.Pushforward.Unit.functor u X.p).obj x)) := sorry

/-- The component in the categorical pullback induced by a vertical transformation between
based functors out of the pushforward. -/
@[stacks 04WI "pushforward unit Hom component"]
noncomputable def mapApp
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    {G H : (FiberedCategoryOver.pushforward u X hX).toBasedCategory ⥤ᵇ Y.toBasedCategory}
    (τ : G ⟶ H) (x : X.total) :
    (obj u G).obj x ⟶ (obj u H).obj x where
  fst := 𝟙 (X.p.obj x)
  snd := τ.toNatTrans.app ((Functor.Pushforward.Unit.functor u X.p).obj x)
  w := mapApp.compatibility u τ x

/-- The components induced by a based natural transformation are natural in the source
object. -/
@[stacks 04WI "pushforward unit Hom component naturality"]
theorem mapApp.naturality
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    {G H : (FiberedCategoryOver.pushforward u X hX).toBasedCategory ⥤ᵇ Y.toBasedCategory}
    (τ : G ⟶ H) {x y : X.total} (f : x ⟶ y) :
    (obj u G).toFunctor.map f ≫ mapApp u τ y =
      mapApp u τ x ≫ (obj u H).toFunctor.map f := sorry

/-- Every component of the induced pullback transformation lies over the identity of its
source base object. -/
@[stacks 04WI "pushforward unit Hom component lift"]
theorem mapApp.isHomLift
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    {G H : (FiberedCategoryOver.pushforward u X hX).toBasedCategory ⥤ᵇ Y.toBasedCategory}
    (τ : G ⟶ H) (x : X.total) :
    (FiberedCategoryOver.pullback u Y).p.IsHomLift (𝟙 (X.p.obj x))
      (mapApp u τ x) := sorry

/-- Lemma 8.12.8 (tag 04WI): the vertical transformation between pullback comparison based
functors induced by a vertical transformation between the original based functors. -/
@[stacks 04WI "pushforward unit Hom map"]
noncomputable def map
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    {G H : (FiberedCategoryOver.pushforward u X hX).toBasedCategory ⥤ᵇ Y.toBasedCategory}
    (τ : G ⟶ H) :
    obj u G ⟶ obj u H where
  toNatTrans :=
    { app := fun x ↦ mapApp u τ x
      naturality := fun {_ _} f ↦ mapApp.naturality u τ f }
  isHomLift' := mapApp.isHomLift u τ

/-- The component of the precomposition transformation is the corresponding morphism in the
categorical pullback. -/
@[simp, stacks 04WI "pushforward unit Hom map component"]
theorem map.app
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    {G H : (FiberedCategoryOver.pushforward u X hX).toBasedCategory ⥤ᵇ Y.toBasedCategory}
    (τ : G ⟶ H) (x : X.total) :
    (map u τ).toNatTrans.app x = mapApp u τ x := sorry

/-- The pullback comparison map preserves identities. -/
@[simp, stacks 04WI "pushforward unit Hom map identity"]
theorem map.id
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (G : (FiberedCategoryOver.pushforward u X hX).toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    map u (𝟙 G) = 𝟙 (obj u G) := sorry

/-- The pullback comparison map preserves vertical composition. -/
@[simp, stacks 04WI "pushforward unit Hom map composition"]
theorem map.comp
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    {G H K : (FiberedCategoryOver.pushforward u X hX).toBasedCategory ⥤ᵇ Y.toBasedCategory}
    (τ : G ⟶ H) (σ : H ⟶ K) :
    map u (τ ≫ σ) = map u τ ≫ map u σ := sorry

/-- Lemma 8.12.8 (tag 04WI): precomposition with the pushforward unit on the category of
based functors, with codomain changed to the categorical pullback. -/
@[stacks 04WI "pushforward unit Hom based functor"]
noncomputable def basedFunctor
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    (hX : ProjectionChoice u X)
    (Y : FiberedCategoryOver.{uD, vD, uY, vY} D) :
    ((FiberedCategoryOver.pushforward u X hX).toBasedCategory ⥤ᵇ Y.toBasedCategory) ⥤
      (X.toBasedCategory ⥤ᵇ (FiberedCategoryOver.pullback u Y).toBasedCategory) where
  obj G := obj u G
  map τ := map u τ
  map_id G := map.id u G
  map_comp τ σ := map.comp u τ σ

/-- The object action of the based precomposition functor is the canonical comparison
`Precompose.obj`. -/
@[simp, stacks 04WI "pushforward unit Hom based functor object"]
theorem basedFunctor.obj
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (G : (FiberedCategoryOver.pushforward u X hX).toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    (basedFunctor u hX Y).obj G = obj u G := sorry

/-- The morphism action of the based precomposition functor is `Precompose.map`. -/
@[simp, stacks 04WI "pushforward unit Hom based functor map"]
theorem basedFunctor.map
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    {G H : (FiberedCategoryOver.pushforward u X hX).toBasedCategory ⥤ᵇ Y.toBasedCategory}
    (τ : G ⟶ H) :
    (basedFunctor u hX Y).map τ = map u τ := sorry

end Precompose

end FiberedCategoryOver.Pushforward

end CategoryTheory
