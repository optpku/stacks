module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Base change of flat morphisms of algebraic spaces

Flat morphisms of algebraic spaces are stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Flat morphisms of algebraic spaces are stable under arbitrary base change. -/
instance flat_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Flat S : MorphismProperty (AlgebraicSpace S)) := sorry

namespace Flat

/-- Flat morphisms of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Flat g) : Flat g' :=
  CategoryTheory.MorphismProperty.of_isPullback sq hg

/-- The base-change projection `pullback.snd f g` of a flat morphism
`f : X ⟶ Y` is flat. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Flat f) (g : Z ⟶ Y) [HasPullback f g] :
    Flat (pullback.snd f g) :=
  CategoryTheory.MorphismProperty.pullback_snd f g hf

/-- The first projection from the pullback of a flat morphism is flat. -/
theorem pullback_fst {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {g : Z ⟶ Y}
    (hg : Flat g) (f : X ⟶ Y) [HasPullback f g] : Flat (pullback.fst f g) :=
  CategoryTheory.MorphismProperty.pullback_fst f g hg

end Flat

/-- The second projection from the pullback of a flat morphism is flat. -/
instance flat_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Flat f] [HasPullback f g] :
    Flat (pullback.snd f g) :=
  Flat.pullback_snd (inferInstance : Flat f) g

/-- The first projection from the pullback of a flat morphism is flat. -/
instance flat_pullback_fst {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Flat g] [HasPullback f g] :
    Flat (pullback.fst f g) :=
  Flat.pullback_fst inferInstance f

end AlgebraicGeometry.AlgebraicSpace
