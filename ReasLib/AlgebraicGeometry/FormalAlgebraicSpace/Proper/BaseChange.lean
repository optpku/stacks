module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Proper

/-!
# Base change of proper morphisms of presheaves over a scheme

Proper morphisms of presheaves over a scheme are stable under arbitrary base
change, in particular for morphisms of formal algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Proper morphisms of presheaves over a scheme are stable under arbitrary base change. -/
instance proper_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Proper S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)) :=
  sorry

namespace Proper

/-- In a pullback square of presheaves over a scheme, the base change of a
proper morphism is proper. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : (Over S)ᵒᵖ ⥤ Type u}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Proper g) : Proper g' :=
  MorphismProperty.of_isPullback (P := @Proper S) sq hg

/-- The base-change projection `pullback.snd f g` of a proper morphism
`f : X ⟶ Y` of presheaves over a scheme is proper. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : Proper f) (g : Z ⟶ Y) [HasPullback f g] :
    Proper (pullback.snd f g) :=
  MorphismProperty.pullback_snd (P := @Proper S) f g hf

end Proper

/-- Pullback projections of proper morphisms of presheaves over a scheme are proper. -/
instance proper_pullback_snd {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y)
    [Proper f] [HasPullback f g] :
    Proper (pullback.snd f g) :=
  Proper.pullback_snd inferInstance g

end AlgebraicGeometry.FormalAlgebraicSpace
