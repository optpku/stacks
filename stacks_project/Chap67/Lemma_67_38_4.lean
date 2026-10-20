module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.BaseChange
import StacksCheckRecall

/-!
# Base change of unramified morphisms of algebraic spaces

The base change of an unramified morphism of algebraic spaces by any morphism of
algebraic spaces is again an unramified morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.38.4: The base change of an unramified morphism is unramified. -/
@[stacks 03ZJ] #check
  (AlgebraicGeometry.AlgebraicSpace.unramified_isStableUnderBaseChange :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
      (@Unramified S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    IsPullback f' g' g f → Unramified g → Unramified g')

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
    Unramified f → ∀ (g : Z ⟶ Y) [HasPullback f g],
      Unramified (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace
