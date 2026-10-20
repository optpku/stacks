module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.SmoothCartesian
import StacksCheckRecall

/-!
# Local dimension comparison on a smooth Cartesian atlas square
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- 107.5.21.1 The full local-dimension chain in a smooth Cartesian square. -/
@[stacks 0DS3] #check (AlgebraicGeometry.AlgebraicStack.dimension_chain_of_smooth_cartesian :
    ∀ {S : Scheme.{u}}
    {X T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack T]
    [IsLocallyNoetherian X] [IsLocallyNoetherian T] {U U' : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    [AlgebraicGeometry.IsLocallyNoetherian U'.left]
    (i : T ⟶ X) (f : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth f]
    (f' : GroupoidsOver.slice U' ⟶ T) [Groupoids.Hom.Smooth f'] (g : U' ⟶ U)
    (iso : overMap g ≫ f ≅ f' ≫ i)
    (h_cart : (CategoryTheory.Bicategory.PseudoPullbackCone.mk f i
      (GroupoidsOver.slice U') (overMap g) f' iso).IsBilimit)
    (u' : U'.left)
    (h_dim : dimensionAt (Points.mapSlice f' u') ≥
      dimensionAt (Points.mapSlice f (g.left u'))),
    (dimensionToEInt (topologicalKrullDimAt u') =
      relativeDimensionAt f' (Points.mk (FieldValuedPoint.ofResidue u')) +
        dimensionAt (Points.mapSlice f' u')) ∧
    (relativeDimensionAt f (Points.mk (FieldValuedPoint.ofResidue (g.left u'))) +
        dimensionAt (Points.mapSlice f (g.left u')) ≤
      relativeDimensionAt f' (Points.mk (FieldValuedPoint.ofResidue u')) +
        dimensionAt (Points.mapSlice f' u')) ∧
    (relativeDimensionAt f (Points.mk (FieldValuedPoint.ofResidue (g.left u'))) +
        dimensionAt (Points.mapSlice f (g.left u')) =
      dimensionToEInt (topologicalKrullDimAt (g.left u'))))

#check (AlgebraicGeometry.AlgebraicStack.dimensionToEInt_le_of_smooth_cartesian :
    ∀ {S : Scheme.{u}}
    {X T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack T]
    [IsLocallyNoetherian X] [IsLocallyNoetherian T] {U U' : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    [AlgebraicGeometry.IsLocallyNoetherian U'.left]
    (i : T ⟶ X) (f : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth f]
    (f' : GroupoidsOver.slice U' ⟶ T) [Groupoids.Hom.Smooth f'] (g : U' ⟶ U)
    (iso : overMap g ≫ f ≅ f' ≫ i)
    (h_cart : (CategoryTheory.Bicategory.PseudoPullbackCone.mk f i
      (GroupoidsOver.slice U') (overMap g) f' iso).IsBilimit)
    (u' : U'.left)
    (h_dim : dimensionAt (Points.mapSlice f' u') ≥
      dimensionAt (Points.mapSlice f (g.left u'))),
    dimensionToEInt (topologicalKrullDimAt (g.left u')) ≤
      dimensionToEInt (topologicalKrullDimAt u'))

#check (AlgebraicGeometry.AlgebraicStack.topologicalKrullDimAt_le_of_smooth_cartesian :
    ∀ {S : Scheme.{u}}
    {X T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack T]
    [IsLocallyNoetherian X] [IsLocallyNoetherian T] {U U' : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    [AlgebraicGeometry.IsLocallyNoetherian U'.left]
    (i : T ⟶ X) (f : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth f]
    (f' : GroupoidsOver.slice U' ⟶ T) [Groupoids.Hom.Smooth f'] (g : U' ⟶ U)
    (iso : overMap g ≫ f ≅ f' ≫ i)
    (h_cart : (CategoryTheory.Bicategory.PseudoPullbackCone.mk f i
      (GroupoidsOver.slice U') (overMap g) f' iso).IsBilimit)
    (u' : U'.left)
    (h_dim : dimensionAt (Points.mapSlice f' u') ≥
      dimensionAt (Points.mapSlice f (g.left u'))),
    topologicalKrullDimAt (g.left u') ≤ topologicalKrullDimAt u')

end AlgebraicGeometry.AlgebraicStack
