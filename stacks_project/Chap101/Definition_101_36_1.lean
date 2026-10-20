module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Unramified
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Definition 101.36.1: a morphism `f : X ⟶ Y` of algebraic stacks is
unramified if it is DM and the equivalent conditions of Lemma 101.34.1
hold with `P` = unramified. -/
@[stacks 0CIT] #check (AlgebraicGeometry.AlgebraicStack.Unramified :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)
