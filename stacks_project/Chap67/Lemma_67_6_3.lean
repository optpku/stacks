module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen
import StacksCheckRecall

/-!
# Base change of universally open morphisms of algebraic spaces

The base change of a universally open morphism of algebraic spaces by any
morphism of algebraic spaces is universally open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.6.3: The base change of a universally open morphism of algebraic
spaces by any morphism of algebraic spaces is universally open. -/
@[stacks 03Z3] #check (AlgebraicGeometry.AlgebraicSpace.UniversallyOpen.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    IsPullback f' g' g f → UniversallyOpen g → UniversallyOpen g')

end AlgebraicGeometry.AlgebraicSpace
