module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.Branch

/-!
# Geometric branch numbers after a field extension

This leaf owns the pointwise geometric-branch-number comparison for the
canonical field-extension base change of a locally algebraic scheme.  It uses
the `Over` presentation so the source point is always the canonical
projection of the target point.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FieldExtension.Over

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable (X : Over (Spec (CommRingCat.of k)))

/-- Geometric branch number is invariant at corresponding
points under field-extension base change of a locally algebraic scheme. -/
@[stacks 0C40]
theorem geometricBranchNumberAt_eq
    [LocallyAlgebraic X]
    (y : (baseChange k K X).left)
    (Ashx : Type u) [CommRing Ashx]
    [Algebra (X.left.presheaf.stalk (toSource k K X y)) Ashx]
    [IsStrictHenselizationOf (X.left.presheaf.stalk (toSource k K X y)) Ashx]
    (Ashy : Type u) [CommRing Ashy]
    [Algebra ((baseChange k K X).left.presheaf.stalk y) Ashy]
    [IsStrictHenselizationOf ((baseChange k K X).left.presheaf.stalk y) Ashy] :
    X.left.geometricBranchNumberAt (toSource k K X y) Ashx =
      (baseChange k K X).left.geometricBranchNumberAt y Ashy := sorry

end

end AlgebraicGeometry.FieldExtension.Over
