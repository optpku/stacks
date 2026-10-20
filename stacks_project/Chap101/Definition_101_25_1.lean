module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- Definition 101.25.1: a morphism `f : X ⟶ Y` of algebraic stacks is
flat if the equivalent conditions of Lemma 101.16.1 hold with `P` = flat. -/
@[stacks 06PW] #check (AlgebraicGeometry.AlgebraicStack.Flat :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y), Prop)
