module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Base change of finite locally free morphisms of algebraic spaces

Finite locally free morphisms of algebraic spaces are stable under arbitrary
base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Finite locally free morphisms of algebraic spaces are stable under arbitrary
base change. -/
instance finiteLocallyFree_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@FiniteLocallyFree S : MorphismProperty (AlgebraicSpace S)) := sorry

namespace FiniteLocallyFree

/-- Finite locally free morphisms of algebraic spaces are stable under pullback
along an arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : FiniteLocallyFree g) :
    FiniteLocallyFree g' :=
  CategoryTheory.MorphismProperty.of_isPullback sq hg

/-- The base-change projection `pullback.snd f g` of a finite locally free
morphism `f : X ⟶ Y` is finite locally free. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : FiniteLocallyFree f) (g : Z ⟶ Y) [HasPullback f g] :
    FiniteLocallyFree (pullback.snd f g) :=
  CategoryTheory.MorphismProperty.pullback_snd f g hf

end FiniteLocallyFree

/-- The base-change projection of a finite locally free morphism is finite
locally free whenever the pullback exists. -/
instance finiteLocallyFree_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [FiniteLocallyFree f] [HasPullback f g] :
    FiniteLocallyFree (pullback.snd f g) :=
  FiniteLocallyFree.pullback_snd inferInstance g

end AlgebraicGeometry.AlgebraicSpace
