module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Branch
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import ReasLib.RingTheory.LocalRing.Branches.Unibranch

/-!
# Geometric unibranchness after a field extension

This leaf owns the pointwise geometric-unibranch comparison for canonical
field-extension base change.  The source point is obtained directly from the
base-change projection.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FieldExtension.Over.Unibranch

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable (X : Over (Spec (CommRingCat.of k)))

/-- Geometric unibranchness is invariant at a base-change point
and its canonical image in a locally algebraic source scheme. -/
@[stacks 0C55]
theorem isGeometricallyUnibranchAt_iff
    [LocallyAlgebraic X]
    (y : (FieldExtension.Over.baseChange k K X).left) :
    X.left.isGeometricallyUnibranchAt (FieldExtension.Over.toSource k K X y) ↔
      (FieldExtension.Over.baseChange k K X).left.isGeometricallyUnibranchAt y := sorry

end AlgebraicGeometry.FieldExtension.Over.Unibranch
