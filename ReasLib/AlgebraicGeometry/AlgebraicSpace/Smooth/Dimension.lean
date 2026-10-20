module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth

/-!
# Dimension formula for smooth morphisms of algebraic spaces

A smooth morphism of locally Noetherian algebraic spaces adds the relative
dimension at a point to the local dimension of the image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Smooth

/-- For a smooth morphism of locally Noetherian algebraic spaces over a scheme,
the dimension at a source point equals the dimension at its image plus the
relative dimension of the morphism at that point. -/
theorem dimensionAt_eq_image_add_fiberDimensionAt
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Smooth f] (x : Points X) :
    dimensionAt x = dimensionAt (Points.map f x) + fiberDimensionAt f x :=
  sorry

/-- If a smooth morphism of locally Noetherian algebraic spaces has relative
dimension `d` at a point, then the local dimension formula holds with addend
`d`. -/
theorem dimensionAt_eq_image_add_of_relativeDimensionAt
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Smooth f] {d : ℕ}
    {x : Points X} (hd : RelativeDimensionAt f d x) :
    dimensionAt x = dimensionAt (Points.map f x) + (d : WithBot ℕ∞) :=
  sorry

end Smooth

end AlgebraicGeometry.AlgebraicSpace
