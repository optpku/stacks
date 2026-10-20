module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiberDimension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeDimension

/-!
# Dimension along smooth morphisms of algebraic stacks

A smooth morphism from an algebraic space to a locally Noetherian algebraic
stack computes the local stack dimension as the difference between the local
source dimension and the relative fibre dimension.
For a smooth morphism of locally Noetherian algebraic stacks, the local source
dimension is the sum of the local image dimension and the relative dimension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The dimension of a locally Noetherian algebraic stack at the image of a
point under a smooth morphism from an algebraic space is the extended-integer
difference of the local source dimension and the relative fibre dimension. -/
@[stacks 0DRJ]
theorem dimensionAt_eq_dimensionDiff_fiberDimensionAt {S : Scheme.{u}}
    {U : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (f : U.toGroupoids ⟶ X)
    [Smooth f] (u : AlgebraicSpace.Points U) :
    dimensionAt (Points.map f (Points.ofAlgebraicSpace u)) =
      dimensionDiff (AlgebraicSpace.dimensionAt u) (fiberDimensionAt f u) := sorry

/-- The dimension of a locally Noetherian algebraic stack at the image of a
point under a smooth morphism from an algebraic space is the extended-integer
difference of the local source dimension and the dimension of any representing
fibre at a lift of that point. -/
theorem dimensionAt_eq_dimensionDiff_of_relativeDimensionChoice {S : Scheme.{u}}
    {U : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (f : U.toGroupoids ⟶ X)
    [Smooth f] (u : AlgebraicSpace.Points U) (w : RelativeDimensionChoice f u) :
    dimensionAt (Points.map f (Points.ofAlgebraicSpace u)) =
      dimensionDiff (AlgebraicSpace.dimensionAt u) w.dimension := sorry

/-- The local dimension at a point of the source of a smooth morphism of
locally Noetherian algebraic stacks is the sum of the local dimension at its
image and the relative dimension at that point. -/
theorem dimensionAt_eq_image_add_relativeDimensionAt {S : Scheme.{u}}
    {U X : GroupoidsOver S} [AlgebraicStack U] [AlgebraicStack X]
    [IsLocallyNoetherian U] [IsLocallyNoetherian X] (f : U ⟶ X)
    [Smooth f] (u : Points U) :
    dimensionAt u = dimensionAt (Points.map f u) + relativeDimensionAt f u := sorry

end AlgebraicGeometry.AlgebraicStack
