module

public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Lemma_67_34_3_FiberDimension
public import stacks_project.Chap67.Lemma_67_37_4_Smooth

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

/-- Lemma 67.37.10: Let `X` and `Y` be locally Noetherian algebraic spaces over
a scheme `S`, and let `f : X ⟶ Y` be a smooth morphism. For every point `x` of
`Points X` with image `y` of `Points Y`, `dimensionAt x = dimensionAt y +
fiberDimensionAt f x`, where `fiberDimensionAt f x` is the relative dimension
of `f` at `x` in the sense of Definition 67.33.1. -/
@[stacks 0AFI]
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
