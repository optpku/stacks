/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.GeometricallyReduced

/-!
# Delta invariants after field extension

These results compare pointwise delta invariants under extension of the base
field, using geometric reducedness and normalization-fiber separability.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.Normalization.DeltaInvariant

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Field extension cannot decrease the pointwise delta invariant at a
geometrically reduced one-dimensional point. -/
@[stacks 0C3X]
theorem le_baseChange
    (X : SchemeOverField k) [LocallyAlgebraic X]
    (x : X.left) (y : (FieldExtension.Over.baseChange k K X).left)
    (hy : FieldExtension.Over.toSource k K X y = x)
    (h_geometricallyReduced : SchemeOverField.geometricallyReducedAt X x)
    (h_dimension_source : ringKrullDim (stalkRing X x) = 1)
    (h_dimension_target :
      ringKrullDim (stalkRing (FieldExtension.Over.baseChange k K X) y) = 1) :
    deltaInvariantAt X x ≤ deltaInvariantAt (FieldExtension.Over.baseChange k K X) y := sorry

/-- After field extension, the pointwise delta invariant is unchanged at a
reduced one-dimensional point when the residue fields in its normalization
fiber are separable over the base field. -/
@[stacks 0C3Y]
theorem eq_baseChange_of_separableFiberResidues
    (X : SchemeOverField k) [LocallyAlgebraic X]
    (x : X.left) [_root_.IsReduced (stalkRing X x)]
    (y : (FieldExtension.Over.baseChange k K X).left)
    (hy : FieldExtension.Over.toSource k K X y = x)
    (h_dimension_source : ringKrullDim (stalkRing X x) = 1)
    (h_separable : FiberResidues.separableAt X x)
    (h_dimension_target :
      ringKrullDim (stalkRing (FieldExtension.Over.baseChange k K X) y) = 1) :
    deltaInvariantAt X x = deltaInvariantAt (FieldExtension.Over.baseChange k K X) y := sorry

end AlgebraicGeometry.SchemeOverField.Normalization.DeltaInvariant
