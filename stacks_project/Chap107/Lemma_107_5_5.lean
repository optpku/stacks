module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.Smooth
import StacksCheckRecall

/-!
# Dimension of a stack via a smooth algebraic-space chart

A smooth morphism from an algebraic space to a locally Noetherian algebraic
stack computes the local stack dimension from the source and fibre dimensions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.5.5: for a smooth morphism f : U.toGroupoids ⟶ X from an
algebraic space to a locally Noetherian algebraic stack, and any point u of
U with image x, the dimension dimensionAt x equals
dimensionDiff (AlgebraicSpace.dimensionAt u) (fiberDimensionAt f u), where
the relative fibre dimension is as in Definition 107.5.2 and the stack
dimension is as in Properties of Stacks, Definition 100.12.2. -/
@[stacks 0DRJ] #check (AlgebraicGeometry.AlgebraicStack.dimensionAt_eq_dimensionDiff_fiberDimensionAt :
  ∀ {S : Scheme.{u}} {U : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (f : U.toGroupoids ⟶ X)
    [Smooth f] (u : AlgebraicSpace.Points U),
    dimensionAt (Points.map f (Points.ofAlgebraicSpace u)) =
      dimensionDiff (AlgebraicSpace.dimensionAt u) (fiberDimensionAt f u))

#check (AlgebraicGeometry.AlgebraicStack.dimensionAt_eq_dimensionDiff_of_relativeDimensionChoice :
  ∀ {S : Scheme.{u}} {U : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (f : U.toGroupoids ⟶ X)
    [Smooth f] (u : AlgebraicSpace.Points U) (w : RelativeDimensionChoice f u),
    dimensionAt (Points.map f (Points.ofAlgebraicSpace u)) =
      dimensionDiff (AlgebraicSpace.dimensionAt u) w.dimension)

end AlgebraicGeometry.AlgebraicStack
