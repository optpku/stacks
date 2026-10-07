module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap65.Lemma_65_12_4_Immersion

/-!
# Base change of immersions of algebraic spaces

Immersions, closed immersions, and open immersions of algebraic spaces are
stable under arbitrary base change. This module records the morphism-level
pullback companions for the existing classes from Lemma 65.12.4.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsImmersion

/-- Immersions of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : IsImmersion g) : IsImmersion g' := sorry

/-- The base-change projection `pullback.snd f g` of an immersion
`f : X ⟶ Y` is an immersion. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsImmersion f) (g : Z ⟶ Y) [HasPullback f g] :
    IsImmersion (pullback.snd f g) := sorry

end IsImmersion

/-- Typeclass form of base-change stability for an immersion along a
morphism for which the pullback exists. -/
instance isImmersion_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsImmersion f] [HasPullback f g] :
    IsImmersion (pullback.snd f g) := sorry

namespace IsClosedImmersion

/-- Closed immersions of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : IsClosedImmersion g) :
    IsClosedImmersion g' := sorry

/-- The base-change projection `pullback.snd f g` of a closed immersion
`f : X ⟶ Y` is a closed immersion. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsClosedImmersion f) (g : Z ⟶ Y) [HasPullback f g] :
    IsClosedImmersion (pullback.snd f g) := sorry

end IsClosedImmersion

/-- Typeclass form of base-change stability for a closed immersion along a
morphism for which the pullback exists. -/
instance isClosedImmersion_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsClosedImmersion f] [HasPullback f g] :
    IsClosedImmersion (pullback.snd f g) := sorry

namespace IsOpenImmersion

/-- Open immersions of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : IsOpenImmersion g) :
    IsOpenImmersion g' := sorry

/-- The base-change projection `pullback.snd f g` of an open immersion
`f : X ⟶ Y` is an open immersion. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsOpenImmersion f) (g : Z ⟶ Y) [HasPullback f g] :
    IsOpenImmersion (pullback.snd f g) := sorry

end IsOpenImmersion

/-- Typeclass form of base-change stability for an open immersion along a
morphism for which the pullback exists. -/
instance isOpenImmersion_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsOpenImmersion f] [HasPullback f g] :
    IsOpenImmersion (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
