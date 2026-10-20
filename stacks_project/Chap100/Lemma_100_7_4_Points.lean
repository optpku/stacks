module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Comparison

/-!
# Scheme and algebraic-space points of an algebraic stack

The canonical point comparisons are provided by the shared mathematical owner.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicStack.Points.mapSpace :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {F : AlgebraicSpace S} (p : F.toGroupoids ⟶ X) (u : AlgebraicSpace.Points F),
    AlgebraicGeometry.AlgebraicStack.Points X)
