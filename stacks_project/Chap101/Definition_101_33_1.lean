module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Definition 101.33.1: a morphism `f : X ⟶ Y` of algebraic stacks is
smooth if the equivalent conditions of Lemma 101.16.1 hold with `P` = smooth.
The existing class uses the existential smooth presentation condition: the
vertical arrows are smooth, the source atlas is surjective, the square is
2-commutative, and the top arrow is smooth. -/
@[stacks 075U] #check (AlgebraicGeometry.AlgebraicStack.Smooth :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y), Prop)
