module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.BaseChange

/-!
# Base change of proper morphisms of algebraic spaces

Proper morphisms of algebraic spaces are stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Proper morphisms of algebraic spaces are stable under arbitrary base change. -/
instance proper_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Proper S : MorphismProperty (AlgebraicSpace S)) := sorry

namespace Proper

/-- Proper morphisms of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Proper g) : Proper g' :=
  MorphismProperty.of_isPullback sq hg

/-- The base-change projection `pullback.snd f g` of a proper morphism
`f : X ⟶ Y` is proper. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Proper f) (g : Z ⟶ Y) [HasPullback f g] :
    Proper (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

end Proper

/-- The pullback projection of a proper morphism is proper. -/
instance proper_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Proper f] [HasPullback f g] :
    Proper (pullback.snd f g) :=
  Proper.pullback_snd inferInstance g

end AlgebraicGeometry.AlgebraicSpace
