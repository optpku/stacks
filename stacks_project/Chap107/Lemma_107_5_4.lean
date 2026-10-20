module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.Dimension
import StacksCheckRecall

/-!
# Dimension formula for smooth morphisms of algebraic spaces

A smooth morphism of locally Noetherian algebraic spaces adds the
Definition 107.5.2 relative dimension at a point to the local dimension of
the image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 107.5.4: if `f : U ⟶ X` is a smooth morphism of locally Noetherian
algebraic spaces, and if `u ∈ |U|` has image `x ∈ |X|`, then
`AlgebraicSpace.dimensionAt u = AlgebraicSpace.dimensionAt x +
AlgebraicSpace.fiberDimensionAt f u`. By Remark 107.5.3(2), this
algebraic-space fibre dimension agrees with Definition 107.5.2. -/
@[stacks 0DRI]
#check (AlgebraicGeometry.AlgebraicSpace.Smooth.dimensionAt_eq_image_add_fiberDimensionAt :
    ∀ {S : Scheme.{u}}
    {U X : AlgebraicSpace S} (f : U ⟶ X)
    [AlgebraicSpace.IsLocallyNoetherian U] [AlgebraicSpace.IsLocallyNoetherian X]
    [AlgebraicSpace.Smooth f] (u : AlgebraicSpace.Points U),
    AlgebraicSpace.dimensionAt u =
      AlgebraicSpace.dimensionAt (AlgebraicSpace.Points.map f u) +
        AlgebraicSpace.fiberDimensionAt f u)
