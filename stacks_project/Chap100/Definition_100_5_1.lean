module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

/- Definition 100.5.1. Let `f : X ⟶ Y` be a morphism of algebraic stacks.
We say `f` is surjective if the map `Points.map f : |X| → |Y|` of associated
topological spaces is surjective. -/
@[stacks 04ZS] #check (AlgebraicGeometry.AlgebraicStack.surjective_iff_map_surjective :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y), AlgebraicGeometry.AlgebraicStack.Surjective f ↔
      Function.Surjective (AlgebraicGeometry.AlgebraicStack.Points.map f))
