module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.ElementaryDistinguishedSquare
import StacksCheckRecall

/-!
# Lemma 81.14.1

Separatedness of a morphism of algebraic spaces can be read off from an
elementary distinguished square whose legs over the target are separated and
whose comparison of fibre products is closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 81.14.1. Let `S` be a scheme. Let `g : X ⟶ Y` be a morphism of algebraic
spaces over `S`. If `(j : U ⟶ X, f : V ⟶ X)` is an elementary distinguished
square such that `U ⟶ Y` and `V ⟶ Y` are separated and
`U ×_X V ⟶ U ×_Y V` is closed, then `X ⟶ Y` is separated. -/
@[stacks 0F45] #check
  (AlgebraicGeometry.AlgebraicSpace.Separated.of_isElementaryDistinguishedSquare :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (g : X ⟶ Y) {U V : AlgebraicSpace S} (j : U ⟶ X) (f : V ⟶ X)
    [IsElementaryDistinguishedSquare j f] [Separated (j ≫ g)] [Separated (f ≫ g)]
    [Closed (pullback.mapDesc j f g)], Separated g)
