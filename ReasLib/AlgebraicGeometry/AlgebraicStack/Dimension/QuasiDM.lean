module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Base

/-!
# Non-negative dimension of quasi-DM algebraic stacks

A locally Noetherian algebraic stack that is quasi-DM over its base has
non-negative dimension at every point. If it has a point, its total dimension
is non-negative as well. A locally of finite type quasi-DM morphism has
non-negative relative dimension at every point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A locally Noetherian algebraic stack which is quasi-DM over its base has
non-negative dimension at every point. -/
theorem dimensionAt_nonneg_of_quasiDM {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X]
    [QuasiDM (baseProjection.{u + 1, u, u + 1} X)] (x : Points X) :
    (0 : EInt) ≤ dimensionAt x :=
  sorry

/-- A nonempty locally Noetherian algebraic stack which is quasi-DM over its
base has non-negative dimension. -/
theorem dimension_nonneg_of_quasiDM {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] [Nonempty (Points X)]
    [QuasiDM (baseProjection.{u + 1, u, u + 1} X)] :
    (0 : EInt) ≤ dimension X :=
  sorry

/-- A locally of finite type quasi-DM morphism of locally Noetherian algebraic
stacks has non-negative relative dimension at every point of the source. -/
theorem relativeDimensionAt_nonneg_of_quasiDM {S : Scheme.{u}}
    {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X]
    {f : T ⟶ X} [LocallyOfFiniteType f] [QuasiDM f] (t : Points T) :
    (0 : EInt) ≤ relativeDimensionAt f t :=
  sorry

end AlgebraicGeometry.AlgebraicStack
