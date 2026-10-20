/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.Smooth

/-!
# Local dimension in smooth Cartesian squares
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- In a smooth Cartesian square over locally Noetherian algebraic stacks, the
local dimensions of the scheme sources are the sums of their relative and base
dimensions. An inequality between the base dimensions gives the corresponding
inequality between these sums. -/
theorem dimension_chain_of_smooth_cartesian {S : Scheme.{u}}
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
      dimensionAt (Points.mapSlice f (g.left u'))) :
    (dimensionToEInt (topologicalKrullDimAt u') =
      relativeDimensionAt f' (Points.mk (FieldValuedPoint.ofResidue u')) +
        dimensionAt (Points.mapSlice f' u')) ∧
    (relativeDimensionAt f (Points.mk (FieldValuedPoint.ofResidue (g.left u'))) +
        dimensionAt (Points.mapSlice f (g.left u')) ≤
      relativeDimensionAt f' (Points.mk (FieldValuedPoint.ofResidue u')) +
        dimensionAt (Points.mapSlice f' u')) ∧
    (relativeDimensionAt f (Points.mk (FieldValuedPoint.ofResidue (g.left u'))) +
        dimensionAt (Points.mapSlice f (g.left u')) =
      dimensionToEInt (topologicalKrullDimAt (g.left u'))) :=
  sorry

/-- In a smooth Cartesian square over locally Noetherian algebraic stacks, an
inequality between the base dimensions gives the same inequality between the
scheme-local dimensions embedded into the extended integers. -/
theorem dimensionToEInt_le_of_smooth_cartesian {S : Scheme.{u}}
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
      dimensionAt (Points.mapSlice f (g.left u'))) :
    dimensionToEInt (topologicalKrullDimAt (g.left u')) ≤
      dimensionToEInt (topologicalKrullDimAt u') :=
  sorry

/-- In a smooth Cartesian square over locally Noetherian algebraic stacks, an
inequality between the base dimensions gives the same inequality between the
local topological Krull dimensions of the scheme sources. -/
theorem topologicalKrullDimAt_le_of_smooth_cartesian {S : Scheme.{u}}
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
      dimensionAt (Points.mapSlice f (g.left u'))) :
    topologicalKrullDimAt (g.left u') ≤ topologicalKrullDimAt u' :=
  sorry

end AlgebraicGeometry.AlgebraicStack
