module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Submersive
import StacksCheckRecall

/-!
# Base change of universally submersive morphisms of algebraic spaces

The base change of a universally submersive morphism of algebraic spaces by any
morphism of algebraic spaces is universally submersive.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.7.3: The base change of a universally submersive morphism of algebraic
spaces by any morphism of algebraic spaces is universally submersive. -/
@[stacks 0CFR]
#check (AlgebraicGeometry.AlgebraicSpace.UniversallySubmersive.of_isPullback :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X Y Y' B : AlgebraicGeometry.AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    CategoryTheory.IsPullback f' g' g f →
      AlgebraicGeometry.AlgebraicSpace.UniversallySubmersive g →
      AlgebraicGeometry.AlgebraicSpace.UniversallySubmersive g')

end AlgebraicGeometry.AlgebraicSpace
