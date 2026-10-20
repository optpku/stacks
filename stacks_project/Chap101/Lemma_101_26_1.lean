module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FlatAt
import StacksCheckRecall

/-!
# Independence of flatness at a point

For a morphism of algebraic stacks, flatness of the top arrow at a point of an
algebraic-space test square is independent of the choice of square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.26.1: Flatness of the top arrow at a point above a fixed source
point is independent of the admissible algebraic-space square. -/
@[stacks 0CIC] #check
  (AlgebraicGeometry.AlgebraicStack.forallFlatAtPointSquare_iff_existsFlatAtPointSquare :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      (x : AlgebraicGeometry.AlgebraicStack.Points X),
      AlgebraicGeometry.AlgebraicStack.forallFlatAtPointSquare f x ↔
        AlgebraicGeometry.AlgebraicStack.existsFlatAtPointSquare f x)
