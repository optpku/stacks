module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection.Composition
import StacksCheckRecall

/-!
# Composition of local complete intersection morphisms of algebraic spaces

A composition of local complete intersection morphisms of algebraic spaces is
a local complete intersection morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.48.5

A composition of local complete intersection morphisms is a local complete
intersection morphism.
-/
@[stacks 06C8] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection.comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [IsLocalCompleteIntersection f] [IsLocalCompleteIntersection g],
      IsLocalCompleteIntersection (f ≫ g))

#check
  (AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection.instIsStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@IsLocalCompleteIntersection S : MorphismProperty (AlgebraicSpace S)))

end AlgebraicGeometry.AlgebraicSpace
