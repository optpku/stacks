/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.OverField.FunctionField
public import ReasLib.FieldTheory.Separable.Generated.GeometricallyReduced

/-!
# Function-Field Criterion for Geometric Reducedness

This leaf relates geometric reducedness of a variety to separability of its
function field over the base field.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The function field of `X`, with the scalar structure induced by `X → Spec k`, is
separable over `k`. -/
def functionFieldIsSeparableOver (X : SchemeOverField k) [Variety X] : Prop :=
  @Algebra.IsSeparableOver k X.left.functionField _ _ (functionFieldAlgebra X)

/-- A variety over a field is geometrically reduced exactly when its function field is
separable over the base field. -/
@[stacks 04KS]
theorem geometricallyReduced_iff_functionField_isSeparableOver
    (X : SchemeOverField k) [Variety X] :
    geometricallyReduced X ↔ functionFieldIsSeparableOver X := sorry

end AlgebraicGeometry.SchemeOverField
