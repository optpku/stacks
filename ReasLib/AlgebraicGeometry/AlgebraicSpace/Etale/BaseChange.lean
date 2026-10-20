module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Base change of étale morphisms of algebraic spaces

Étale morphisms of algebraic spaces are stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Étale morphisms of algebraic spaces are stable under base change. -/
instance instIsStableUnderBaseChange_etale {S : Scheme.{u}} :
    IsStableUnderBaseChange (@Etale S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

namespace Etale

/-- Étale morphisms of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Etale g) : Etale g' :=
  MorphismProperty.of_isPullback sq hg

/-- The base-change projection `pullback.snd f g` of an étale morphism
`f : X ⟶ Y` is étale. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Etale f) (g : Z ⟶ Y) [HasPullback f g] :
    Etale (pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ hf

/-- The base-change projection `pullback.fst f g` of an étale morphism
`g : Z ⟶ Y` is étale. -/
theorem pullback_fst {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
    {g : Z ⟶ Y} (hg : Etale g) [HasPullback f g] :
    Etale (pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ hg

/-- Typeclass form of base-change stability for an étale morphism along a
morphism for which the pullback exists. -/
instance instPullbackSnd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Etale f] [HasPullback f g] :
    Etale (pullback.snd f g) :=
  pullback_snd inferInstance g

/-- Typeclass form of base-change stability for the first projection of a
pullback of an étale morphism. -/
instance instPullbackFst {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Etale g] [HasPullback f g] :
    Etale (pullback.fst f g) :=
  pullback_fst f inferInstance

end Etale

end AlgebraicGeometry.AlgebraicSpace
