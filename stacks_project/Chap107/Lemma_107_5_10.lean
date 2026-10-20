module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.Smooth
import StacksCheckRecall

/-!
# Dimension formula for smooth morphisms of algebraic stacks

A smooth morphism of locally Noetherian algebraic stacks adds the
Definition 107.5.7 relative dimension at a point to the local dimension of
the image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.5.10: if `f : U ⟶ X` is a smooth morphism of locally Noetherian
algebraic stacks, and if `u ∈ |U|` has image `x ∈ |X|`, then
`dimensionAt u = dimensionAt x + relativeDimensionAt f u`, where
`relativeDimensionAt` is the relative dimension of Definition 107.5.7. -/
@[stacks 0DRP] #check
  (AlgebraicGeometry.AlgebraicStack.dimensionAt_eq_image_add_relativeDimensionAt :
    ∀ {S : Scheme.{u}} {U X : GroupoidsOver S}
      [AlgebraicStack U] [AlgebraicStack X]
      [IsLocallyNoetherian U] [IsLocallyNoetherian X]
      (f : U ⟶ X) [Smooth f] (u : Points U),
      dimensionAt u = dimensionAt (Points.map f u) + relativeDimensionAt f u)

end AlgebraicGeometry.AlgebraicStack
