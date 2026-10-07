module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Lemma_67_37_6
public import stacks_project.Chap107.Remark_107_5_3_RelativeDimension

/-!
# Dimension formula for smooth morphisms of algebraic spaces

A smooth morphism of locally Noetherian algebraic spaces adds the
Definition 107.5.2 relative dimension at a point to the local dimension of
the image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 107.5.4: if `f : U ⟶ X` is a smooth morphism of locally Noetherian
algebraic spaces, and if `u ∈ |U|` has image `x ∈ |X|`, then
`AlgebraicSpace.dimensionAt u = AlgebraicSpace.dimensionAt x +
fiberDimensionAt (AlgebraicSpace.toGroupoids.map f) u`, where
`fiberDimensionAt` is the relative dimension of Definition 107.5.2. -/
@[stacks 0DRI]
theorem dimensionAt_eq_image_add_fiberDimensionAt {S : Scheme.{u}}
    {U X : AlgebraicSpace S} (f : U ⟶ X)
    [AlgebraicSpace.IsLocallyNoetherian U] [AlgebraicSpace.IsLocallyNoetherian X]
    [AlgebraicSpace.Smooth f] (u : AlgebraicSpace.Points U) :
    AlgebraicSpace.dimensionAt u =
      AlgebraicSpace.dimensionAt (AlgebraicSpace.Points.map f u) +
        fiberDimensionAt (AlgebraicSpace.toGroupoids.map f) u :=
  sorry

/-- The smooth dimension formula with a representing fibre for
`dim_u(U_x)` as the addend. -/
theorem dimensionAt_eq_image_add_of_relativeDimensionChoice {S : Scheme.{u}}
    {U X : AlgebraicSpace S} (f : U ⟶ X)
    [AlgebraicSpace.IsLocallyNoetherian U] [AlgebraicSpace.IsLocallyNoetherian X]
    [AlgebraicSpace.Smooth f] (u : AlgebraicSpace.Points U)
    (w : RelativeDimensionChoice (AlgebraicSpace.toGroupoids.map f) u) :
    AlgebraicSpace.dimensionAt u =
      AlgebraicSpace.dimensionAt (AlgebraicSpace.Points.map f u) + w.dimension :=
  sorry

end AlgebraicGeometry.AlgebraicStack
