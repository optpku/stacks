module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Base change of immersions of algebraic spaces

Immersions, closed immersions, and open immersions of algebraic spaces over a
scheme are stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The base change of an immersion of algebraic spaces is an
immersion. -/
instance isImmersion_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@IsImmersion S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The base change of a closed immersion of algebraic spaces
is a closed immersion. -/
instance isClosedImmersion_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The base change of an open immersion of algebraic spaces
is an open immersion. -/
instance isOpenImmersion_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@IsOpenImmersion S : MorphismProperty (AlgebraicSpace S)) := sorry

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

/-- The second projection of a pullback of an immersion is an immersion. -/
instance isImmersion_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsImmersion f] [HasPullback f g] :
    IsImmersion (pullback.snd f g) := sorry

namespace IsClosedImmersion

/-- The base-change projection `pullback.snd f g` of a closed immersion
`f : X ⟶ Y` is a closed immersion. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsClosedImmersion f) (g : Z ⟶ Y) [HasPullback f g] :
    IsClosedImmersion (pullback.snd f g) := sorry

end IsClosedImmersion

/-- The second projection of a pullback of a closed immersion is a closed immersion. -/
instance isClosedImmersion_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsClosedImmersion f] [HasPullback f g] :
    IsClosedImmersion (pullback.snd f g) := sorry

namespace IsOpenImmersion

/-- The base-change projection `pullback.snd f g` of an open immersion
`f : X ⟶ Y` is an open immersion. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsOpenImmersion f) (g : Z ⟶ Y) [HasPullback f g] :
    IsOpenImmersion (pullback.snd f g) := sorry

end IsOpenImmersion

/-- The second projection of a pullback of an open immersion is an open immersion. -/
instance isOpenImmersion_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsOpenImmersion f] [HasPullback f g] :
    IsOpenImmersion (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
