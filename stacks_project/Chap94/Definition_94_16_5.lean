module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Presentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 94.16.5: a presentation of an algebraic stack X over S is given by a
smooth groupoid (U, R, s, t, c) in algebraic spaces over S, and an equivalence
f : [U / R] ⟶ X. -/
@[stacks 04TI] #check (AlgebraicGeometry.AlgebraicStack.Presentation :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Type (u + 1))
