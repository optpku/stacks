module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Hom.Cartesian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback comparison after a pushforward projection

An explicit projection choice for pushforward and a cartesian comparison out of that pushforward
determine a comparison from the original fibred category to the pullback of the target.  This is
the heterogeneous data owner used by inverse-image stack constructions.
-/

@[expose] public section

universe uC uD vC vD uX vX uY vY

namespace CategoryTheory

open Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

namespace CartesianBasedFunctor.PushforwardHom

/-- Lemma 8.12.12 (1) (tag 04WS), neutral data owner: a cartesian comparison out of a chosen
pushforward induces a heterogeneous comparison into the pullback of its target. -/
@[stacks 04WS "heterogeneous pushforward-pullback comparison"]
noncomputable def pullbackComparison
    {u : C ⥤ D} [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : FiberedCategoryOver.Pushforward.ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (i : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p) :
    CartesianBasedFunctor X.p (FiberedCategoryOver.pullback u Y).p :=
  FiberedCategoryOver.Pushforward.CartesianHom.obj (hX := hX) u i

/-- Forgetting the neutral pullback comparison to a based functor recovers precomposition with
the pushforward unit. -/
@[simp, stacks 04WS "heterogeneous pushforward-pullback based computation"]
theorem pullbackComparison.toBasedFunctor
    {u : C ⥤ D} [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : FiberedCategoryOver.Pushforward.ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (i : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p) :
    (pullbackComparison i).toBasedFunctor =
      FiberedCategoryOver.Pushforward.Precompose.obj (hX := hX) u i.toBasedFunctor := sorry

/-- The total functor of the neutral pullback comparison is the ordinary comparison functor
obtained by precomposing with the pushforward unit. -/
@[simp, stacks 04WS "heterogeneous pushforward-pullback total computation"]
theorem pullbackComparison.toFunctor
    {u : C ⥤ D} [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
    {hX : FiberedCategoryOver.Pushforward.ProjectionChoice u X}
    {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
    (i : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p) :
    (pullbackComparison i).toFunctor =
      FiberedCategoryOver.Pushforward.Precompose.functor (hX := hX) u i.toBasedFunctor := sorry

/- Axiom audit: `pullbackComparison` is exactly the neutral cartesian Hom construction applied to
the supplied projection choice and comparison; it introduces no choice or proof-derived data. -/

end CartesianBasedFunctor.PushforwardHom

end CategoryTheory
