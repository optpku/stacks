module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Proper.ClosedImmersion
import StacksCheckRecall

/-!
# Closed immersions of algebraic stacks are proper

A closed immersion of algebraic stacks is a proper morphism of algebraic
stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.37.4: A closed immersion of algebraic stacks is a proper morphism
of algebraic stacks. -/
@[stacks 0CL8] #check (AlgebraicGeometry.AlgebraicStack.Proper.of_closedImmersion :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Groupoids.Hom.ClosedImmersion f],
    AlgebraicGeometry.AlgebraicStack.Proper f)
