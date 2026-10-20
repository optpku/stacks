module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Base change of locally finitely presented algebraic-space morphisms

Morphisms of algebraic spaces locally of finite presentation are stable under
arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Morphisms of algebraic spaces locally of finite presentation are stable
under arbitrary base change. -/
instance locallyOfFinitePresentation_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S)) :=
    sorry

namespace LocallyOfFinitePresentation

/-- Locally-of-finite-presentation morphisms of algebraic spaces are stable
under pullback along an arbitrary morphism, expressed by an `IsPullback`
square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : LocallyOfFinitePresentation g) :
    LocallyOfFinitePresentation g' := sorry

/-- The base-change projection `pullback.snd f g` of a
locally-of-finite-presentation morphism `f : X ⟶ Y` is locally of finite
presentation. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) (g : Z ⟶ Y) [HasPullback f g] :
    LocallyOfFinitePresentation (pullback.snd f g) := sorry

end LocallyOfFinitePresentation

/-- Typeclass form of base-change stability for a
locally-of-finite-presentation morphism along a morphism for which the
pullback exists. -/
instance locallyOfFinitePresentation_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [LocallyOfFinitePresentation f] [HasPullback f g] :
    LocallyOfFinitePresentation (pullback.snd f g) := sorry

/-- The first projection from a pullback of a locally finitely presented morphism
is locally of finite presentation. -/
instance locallyOfFinitePresentation_pullback_fst {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [LocallyOfFinitePresentation g] [HasPullback f g] :
    LocallyOfFinitePresentation (pullback.fst f g) :=
  CategoryTheory.MorphismProperty.pullback_fst (P := @LocallyOfFinitePresentation S)
    f g inferInstance

end AlgebraicGeometry.AlgebraicSpace
