/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Hom.Precompose
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushforward-pullback on cartesian Hom categories

This leaf restricts unit precomposition to cartesian based functors. Its functor and equivalence
are universe-polymorphic in the two total categories; the fixed `FiberedCategoryOver` bridge is
kept in the later `Hom.Fibered` leaf.
-/

@[expose] public section

universe uC uD vC vD uX vX uY vY

namespace CategoryTheory

open Limits

namespace FiberedCategoryOver.Pushforward

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

namespace CartesianHom

/-- Precomposition with the pushforward unit preserves strongly cartesian arrows. The input is
universe-polymorphic, so the source and target total categories need not share a universe. -/
@[stacks 04WI "cartesian Hom precomposition preserves strongly cartesian arrows"]
theorem precomposePreservesStronglyCartesian
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (G : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p) :
    (Precompose.obj (hX := hX) u G.toBasedFunctor).PreservesStronglyCartesian := sorry

/-- The cartesian based functor obtained by precomposing with the pushforward unit. -/
@[stacks 04WI "cartesian Hom precomposition object"]
noncomputable def obj
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (G : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p) :
    CartesianBasedFunctor X.p (FiberedCategoryOver.pullback u Y).p :=
  ⟨Precompose.obj (hX := hX) u G.toBasedFunctor,
    precomposePreservesStronglyCartesian (hX := hX) u G⟩

/-- Forgetting the cartesian structure from the precomposition object recovers the underlying
based comparison functor. -/
@[simp, stacks 04WI "cartesian Hom precomposition based computation"]
theorem obj.toBasedFunctor
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (G : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p) :
    (obj (hX := hX) u G).toBasedFunctor =
      Precompose.obj (hX := hX) u G.toBasedFunctor := sorry

/-- Forgetting to total categories from the precomposition object recovers the categorical-
pullback comparison functor. -/
@[simp, stacks 04WI "cartesian Hom precomposition total computation"]
theorem obj.toFunctor
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (G : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p) :
    (obj (hX := hX) u G).toFunctor =
      Precompose.functor (hX := hX) u G.toBasedFunctor := sorry

/-- The vertical transformation obtained by precomposing a morphism of cartesian based functors
with the pushforward unit. -/
@[stacks 04WI "cartesian Hom precomposition map"]
noncomputable def map
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    {G H : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p}
    (τ : G ⟶ H) : obj (hX := hX) u G ⟶ obj (hX := hX) u H :=
  CartesianBasedFunctor.homMk (Precompose.map (hX := hX) u τ.hom)

/-- Forgetting the cartesian packaging from a precomposition map recovers the underlying based
natural transformation. -/
@[simp, stacks 04WI "cartesian Hom precomposition map based computation"]
theorem map.toBasedNatTrans
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    {G H : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p}
    (τ : G ⟶ H) :
    CartesianBasedFunctor.toBasedNatTrans (map (hX := hX) u τ) =
      Precompose.map (hX := hX) u τ.hom := sorry

/-- The component of a cartesian precomposition map is the component of the underlying based
comparison transformation. -/
@[simp, stacks 04WI "cartesian Hom precomposition map component"]
theorem map.app
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    {G H : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p}
    (τ : G ⟶ H) (x : X.total) :
    (CartesianBasedFunctor.toBasedNatTrans (map (hX := hX) u τ)).toNatTrans.app x =
      Precompose.mapApp (hX := hX) u τ.hom x := sorry

/-- Precomposition on cartesian based functors preserves identity transformations. -/
@[simp, stacks 04WI "cartesian Hom precomposition identity"]
theorem map.id
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (G : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p) :
    map (hX := hX) u (𝟙 G) = 𝟙 (obj (hX := hX) u G) := sorry

/-- Precomposition on cartesian based functors preserves vertical composition. -/
@[simp, stacks 04WI "cartesian Hom precomposition composition"]
theorem map.comp
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    {G H K : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p}
    (τ : G ⟶ H) (σ : H ⟶ K) :
    map (hX := hX) u (τ ≫ σ) =
      map (hX := hX) u τ ≫ map (hX := hX) u σ := sorry

/-- Lemma 8.12.8 (tag 04WI): the universe-polymorphic Hom functor induced by precomposition
with the pushforward unit, restricted to cartesian based functors. -/
@[stacks 04WI "universe-polymorphic pushforward-pullback Hom functor"]
noncomputable def functor
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    (hX : ProjectionChoice u X)
    (Y : FiberedCategoryOver.{uD, vD, uY, vY} D) :
    CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p ⥤
      CartesianBasedFunctor X.p (FiberedCategoryOver.pullback u Y).p where
  obj := obj (hX := hX) u
  map := map (hX := hX) u
  map_id := map.id (hX := hX) u
  map_comp := map.comp (hX := hX) u

namespace functor

/-- The object action of the cartesian Hom functor is `CartesianHom.obj`. -/
@[simp, stacks 04WI "cartesian Hom functor object computation"]
theorem obj
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (G : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p) :
    (CartesianHom.functor u hX Y).obj G =
      CartesianHom.obj (hX := hX) u G := sorry

/-- The morphism action of the cartesian Hom functor is `CartesianHom.map`. -/
@[simp, stacks 04WI "cartesian Hom functor map computation"]
theorem map
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    {G H : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p}
    (τ : G ⟶ H) :
    (CartesianHom.functor u hX Y).map τ =
      CartesianHom.map (hX := hX) u τ := sorry

/-- Lemma 8.12.8 (tag 04WI): the universe-polymorphic pushforward-pullback Hom functor on
cartesian based functors is an equivalence. This is the neutral owner of the equivalence; no
common universe for the source and target total categories is required. -/
@[stacks 04WI "universe-polymorphic pushforward-pullback Hom equivalence"]
instance isEquivalence
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    (hX : ProjectionChoice u X)
    (Y : FiberedCategoryOver.{uD, vD, uY, vY} D) :
    (CartesianHom.functor u hX Y).IsEquivalence := sorry

end functor

end CartesianHom

end FiberedCategoryOver.Pushforward

end CategoryTheory
