module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection.BaseChange

/-!
# Flat base change of local complete intersection morphisms of algebraic spaces

A flat base change of a local complete intersection morphism of algebraic
spaces is a local complete intersection morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.48.4: A flat base change of a local complete intersection morphism
is a local complete intersection morphism. -/
@[stacks 06C7] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection.pullback_snd :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
      [IsLocalCompleteIntersection f] [Flat g],
      IsLocalCompleteIntersection (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace
