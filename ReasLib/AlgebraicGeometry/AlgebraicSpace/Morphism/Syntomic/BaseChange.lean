module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic

/-!
# Base change of syntomic morphisms of algebraic spaces

Syntomic morphisms of algebraic spaces are stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Syntomic morphisms of algebraic spaces are stable under arbitrary base change. -/
instance syntomic_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Syntomic S : MorphismProperty (AlgebraicSpace S)) := sorry

namespace Syntomic

/-- Syntomic morphisms of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Syntomic g) : Syntomic g' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (@Syntomic S : MorphismProperty (AlgebraicSpace S))) sq hg

/-- The base-change projection `pullback.snd f g` of a syntomic morphism
`f : X ⟶ Y` is syntomic. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Syntomic f) (g : Z ⟶ Y) [HasPullback f g] :
    Syntomic (pullback.snd f g) :=
  MorphismProperty.pullback_snd
    (P := (@Syntomic S : MorphismProperty (AlgebraicSpace S))) f g hf

end Syntomic

/-- The second projection from the pullback of a syntomic morphism is syntomic. -/
instance syntomic_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Syntomic f] [HasPullback f g] :
    Syntomic (pullback.snd f g) :=
  Syntomic.pullback_snd (inferInstance : Syntomic f) g

end AlgebraicGeometry.AlgebraicSpace
