/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_12_3_Dimension
public import stacks_project.Chap100.Lemma_100_4_3_Comparison
public import stacks_project.Chap100.Lemma_100_11_3_LocallyNoetherian

/-!
# Local dimension comparison on a smooth 2-cartesian atlas square

Pulling a smooth scheme atlas of a locally Noetherian algebraic stack back along
a morphism of locally Noetherian algebraic stacks cannot decrease local
dimension at corresponding scheme points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- 107.5.21.1 In a 2-cartesian square of locally Noetherian algebraic stacks whose
scheme-atlas legs `f : GroupoidsOver.slice U ⟶ X` and
`f' : GroupoidsOver.slice U' ⟶ T` are smooth, with scheme map `g : U' ⟶ U` and
2-iso `overMap g ≫ f ≅ f' ≫ i`, the local dimensions satisfy
`topologicalKrullDimAt (g.left u') ≤ topologicalKrullDimAt u'` whenever
`dimensionAt (Points.mapSlice f' u') ≥ dimensionAt (Points.mapSlice f (g.left u'))`.
The source chain is
`dimensionToEInt (topologicalKrullDimAt u') =
  relativeDimensionAt f' (Points.mk (FieldValuedPoint.ofResidue u')) +
    dimensionAt (Points.mapSlice f' u')`,
which is `≥`
`relativeDimensionAt f (Points.mk (FieldValuedPoint.ofResidue (g.left u'))) +
  dimensionAt (Points.mapSlice f (g.left u'))`
`= dimensionToEInt (topologicalKrullDimAt (g.left u'))`,
where the middle step is `relativeDimensionAt_eq_of_isBilimit` plus `h_dim`.
Here `dim_u'(U'_{f(u')})` denotes that `relativeDimensionAt`, not the
difference of local dimensions of `U'` and `T`. -/
@[stacks 0DS3]
theorem topologicalKrullDimAt_le_of_smooth_cartesian {S : Scheme.{u}}
    {X T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack T]
    [IsLocallyNoetherian X] [IsLocallyNoetherian T] {U U' : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    [AlgebraicGeometry.IsLocallyNoetherian U'.left]
    (i : T ⟶ X) (f : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth f]
    (f' : GroupoidsOver.slice U' ⟶ T) [Groupoids.Hom.Smooth f'] (g : U' ⟶ U)
    (iso : overMap g ≫ f ≅ f' ≫ i) (h_cart : (Points.cone iso).IsBilimit)
    (u' : U'.left)
    (h_dim : dimensionAt (Points.mapSlice f' u') ≥
      dimensionAt (Points.mapSlice f (g.left u'))) :
    topologicalKrullDimAt (g.left u') ≤ topologicalKrullDimAt u' :=
  sorry

/-- The `dimensionToEInt` form of the smooth 2-cartesian local-dimension
comparison, for mixing scheme-local dimensions with `dimensionAt`. -/
theorem dimensionToEInt_le_of_smooth_cartesian {S : Scheme.{u}}
    {X T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack T]
    [IsLocallyNoetherian X] [IsLocallyNoetherian T] {U U' : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    [AlgebraicGeometry.IsLocallyNoetherian U'.left]
    (i : T ⟶ X) (f : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth f]
    (f' : GroupoidsOver.slice U' ⟶ T) [Groupoids.Hom.Smooth f'] (g : U' ⟶ U)
    (iso : overMap g ≫ f ≅ f' ≫ i) (h_cart : (Points.cone iso).IsBilimit)
    (u' : U'.left)
    (h_dim : dimensionAt (Points.mapSlice f' u') ≥
      dimensionAt (Points.mapSlice f (g.left u'))) :
    dimensionToEInt (topologicalKrullDimAt (g.left u')) ≤
      dimensionToEInt (topologicalKrullDimAt u') :=
  sorry

end AlgebraicGeometry.AlgebraicStack
