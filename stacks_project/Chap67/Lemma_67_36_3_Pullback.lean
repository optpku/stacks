module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap67.Lemma_67_36_4_Syntomic

/-!
# Base change of syntomic morphisms of algebraic spaces

Syntomic morphisms of algebraic spaces are stable under arbitrary base change.
This module records the morphism-level pullback companions for the existing
`Syntomic` class from Definition 67.36.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Syntomic

/-- Syntomic morphisms of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Syntomic g) : Syntomic g' := sorry

/-- The base-change projection `pullback.snd f g` of a syntomic morphism
`f : X ⟶ Y` is syntomic. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Syntomic f) (g : Z ⟶ Y) [HasPullback f g] :
    Syntomic (pullback.snd f g) := sorry

end Syntomic

/-- Typeclass form of base-change stability for a syntomic morphism along a
morphism for which the pullback exists. -/
instance syntomic_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Syntomic f] [HasPullback f g] :
    Syntomic (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
