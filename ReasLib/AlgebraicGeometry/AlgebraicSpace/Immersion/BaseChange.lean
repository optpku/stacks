/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
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

private theorem isPullback_functorOfPoints {S : Scheme.{u}}
    {P X Y Z : AlgebraicSpace S} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback fst snd f g) :
    IsPullback (C := (Over S)ᵒᵖ ⥤ Type u)
      (fst : P.functorOfPoints ⟶ X.functorOfPoints) snd f g := by
  let F : AlgebraicSpace S ⥤ ((Over S)ᵒᵖ ⥤ Type u) :=
    { obj := fun X ↦ X.functorOfPoints
      map := fun f ↦ f }
  letI : PreservesLimit (cospan f g) F :=
    (ReasLibPullback.isPullback f g).preservesLimit_cospan_iff.mpr
      (IsPullback.of_hasPullback (C := (Over S)ᵒᵖ ⥤ Type u)
        (f : X.functorOfPoints ⟶ Z.functorOfPoints)
        (g : Y.functorOfPoints ⟶ Z.functorOfPoints))
  exact sq.map F

/-- The base change of an immersion of algebraic spaces is an
immersion. -/
instance isImmersion_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@IsImmersion S : MorphismProperty (AlgebraicSpace S)) where
  of_isPullback sq hg :=
    ⟨(MorphismProperty.relative_isStableUnderBaseChange
      (over (@AlgebraicGeometry.IsImmersion : MorphismProperty Scheme.{u}))).of_isPullback
        (isPullback_functorOfPoints sq) hg.presheaf⟩

/-- The base change of a closed immersion of algebraic spaces
is a closed immersion. -/
instance isClosedImmersion_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S)) where
  of_isPullback sq hg :=
    ⟨(MorphismProperty.relative_isStableUnderBaseChange
      (over (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u}))).of_isPullback
        (isPullback_functorOfPoints sq) hg.presheaf⟩

/-- The base change of an open immersion of algebraic spaces
is an open immersion. -/
instance isOpenImmersion_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@IsOpenImmersion S : MorphismProperty (AlgebraicSpace S)) where
  of_isPullback sq hg :=
    ⟨(MorphismProperty.relative_isStableUnderBaseChange
      (over (@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u}))).of_isPullback
        (isPullback_functorOfPoints sq) hg.presheaf⟩

namespace IsImmersion

/-- Immersions of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : IsImmersion g) : IsImmersion g' :=
  MorphismProperty.of_isPullback sq hg

/-- The base-change projection `pullback.snd f g` of an immersion
`f : X ⟶ Y` is an immersion. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsImmersion f) (g : Z ⟶ Y) [HasPullback f g] :
    IsImmersion (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

end IsImmersion

/-- The second projection of a pullback of an immersion is an immersion. -/
instance isImmersion_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsImmersion f] [HasPullback f g] :
    IsImmersion (pullback.snd f g) :=
  IsImmersion.pullback_snd ‹IsImmersion f› g

namespace IsClosedImmersion

/-- The base-change projection `pullback.snd f g` of a closed immersion
`f : X ⟶ Y` is a closed immersion. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsClosedImmersion f) (g : Z ⟶ Y) [HasPullback f g] :
    IsClosedImmersion (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

end IsClosedImmersion

/-- The second projection of a pullback of a closed immersion is a closed immersion. -/
instance isClosedImmersion_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsClosedImmersion f] [HasPullback f g] :
    IsClosedImmersion (pullback.snd f g) :=
  IsClosedImmersion.pullback_snd ‹IsClosedImmersion f› g

namespace IsOpenImmersion

/-- The base-change projection `pullback.snd f g` of an open immersion
`f : X ⟶ Y` is an open immersion. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsOpenImmersion f) (g : Z ⟶ Y) [HasPullback f g] :
    IsOpenImmersion (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

end IsOpenImmersion

/-- The second projection of a pullback of an open immersion is an open immersion. -/
instance isOpenImmersion_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsOpenImmersion f] [HasPullback f g] :
    IsOpenImmersion (pullback.snd f g) :=
  IsOpenImmersion.pullback_snd ‹IsOpenImmersion f› g

end AlgebraicGeometry.AlgebraicSpace
