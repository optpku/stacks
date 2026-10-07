module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap76.Lemma_76_14_4_FormallyUnramified

/-!
# Base change of formally unramified morphisms of algebraic spaces

Formally unramified morphisms of algebraic spaces are stable under arbitrary
base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormallyUnramified

/-- Formally unramified morphisms of algebraic spaces are stable under
arbitrary base change. -/
instance instIsStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@FormallyUnramified S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- The base-change projection `pullback.snd f g` of a formally unramified
morphism `f : X ⟶ Y` is formally unramified. -/
instance pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [FormallyUnramified f] :
    FormallyUnramified (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormallyUnramified
