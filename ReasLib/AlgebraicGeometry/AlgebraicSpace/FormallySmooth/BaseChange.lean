module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth

/-!
# Base change of formally smooth morphisms of algebraic spaces

Formally smooth morphisms of algebraic spaces are stable under arbitrary
base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormallySmooth

/-- Formally smooth morphisms of algebraic spaces are stable under
arbitrary base change. -/
instance instIsStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@FormallySmooth S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- The base-change projection `pullback.snd f g` of a formally smooth
morphism `f : X ⟶ Y` is formally smooth. -/
instance pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [FormallySmooth f] :
    FormallySmooth (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormallySmooth
