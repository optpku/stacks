module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.BaseChange

/-!
# Base change of finitely presented algebraic-space morphisms

Morphisms of algebraic spaces of finite presentation are stable under
arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Morphisms of algebraic spaces of finite presentation are stable under
arbitrary base change. -/
instance finitePresentation_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@FinitePresentation S : MorphismProperty (AlgebraicSpace S)) := sorry

namespace FinitePresentation

/-- Finite-presentation morphisms of algebraic spaces are stable under pullback
along an arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : FinitePresentation g) :
    FinitePresentation g' := sorry

/-- The base-change projection `pullback.snd f g` of a finite-presentation
morphism `f : X ⟶ Y` is of finite presentation. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : FinitePresentation f) (g : Z ⟶ Y) [HasPullback f g] :
    FinitePresentation (pullback.snd f g) := sorry

end FinitePresentation

/-- Typeclass form of base-change stability for a finite-presentation morphism
along a morphism for which the pullback exists. -/
instance finitePresentation_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [FinitePresentation f] [HasPullback f g] :
    FinitePresentation (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
