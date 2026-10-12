/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.Admissible.Decomposition
public import ReasLib.CategoryTheory.ObjectProperty.Orthogonal.Retract
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Orthogonals of Admissible Subcategories

Adjointability identifies a subcategory, or its strict-full closure, with a
double orthogonal.  Retract closure is then exposed as a consequence of the
canonical orthogonal owner.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory.ObjectProperty.Admissible

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (A : ObjectProperty D) [A.IsTriangulated]

namespace Right

/-- Stacks 0CQS: if the inclusion of `A` has a right adjoint, the strict-full
closure of `A` is the left orthogonal of `A.rightOrthogonal`. -/
@[stacks 0CQS]
theorem isoClosure_eq (hA : A.ι.IsLeftAdjoint) :
    A.isoClosure = A.rightOrthogonal.leftOrthogonal := sorry

/-- Stacks 0CQS: right adjointability makes the strict-full closure of `A`
stable under retracts. -/
@[stacks 0CQS]
theorem isoClosure_closedUnderRetracts (hA : A.ι.IsLeftAdjoint) :
    A.isoClosure.IsStableUnderRetracts := sorry

/-- Stacks 0CQS: a strictly full right-adjointable subcategory is the left
orthogonal of its right orthogonal. -/
@[stacks 0CQS]
theorem eq_leftOrthogonal [A.IsClosedUnderIsomorphisms]
    (hA : A.ι.IsLeftAdjoint) :
    A = A.rightOrthogonal.leftOrthogonal := sorry

/-- Stacks 0CQS: a strictly full right-adjointable subcategory is stable under
retracts. -/
@[stacks 0CQS]
theorem closedUnderRetracts [A.IsClosedUnderIsomorphisms]
    (hA : A.ι.IsLeftAdjoint) :
    A.IsStableUnderRetracts := sorry

end Right

namespace Left

/-- Stacks 0CQT: if the inclusion of `A` has a left adjoint, the strict-full
closure of `A` is the right orthogonal of `A.leftOrthogonal`. -/
@[stacks 0CQT]
theorem isoClosure_eq (hA : A.ι.IsRightAdjoint) :
    A.isoClosure = A.leftOrthogonal.rightOrthogonal := sorry

/-- Stacks 0CQT: left adjointability makes the strict-full closure of `A`
stable under retracts. -/
@[stacks 0CQT]
theorem isoClosure_closedUnderRetracts (hA : A.ι.IsRightAdjoint) :
    A.isoClosure.IsStableUnderRetracts := sorry

/-- Stacks 0CQT: a strictly full left-adjointable subcategory is the right
orthogonal of its left orthogonal. -/
@[stacks 0CQT]
theorem eq_rightOrthogonal [A.IsClosedUnderIsomorphisms]
    (hA : A.ι.IsRightAdjoint) :
    A = A.leftOrthogonal.rightOrthogonal := sorry

/-- Stacks 0CQT: a strictly full left-adjointable subcategory is stable under
retracts. -/
@[stacks 0CQT]
theorem closedUnderRetracts [A.IsClosedUnderIsomorphisms]
    (hA : A.ι.IsRightAdjoint) :
    A.IsStableUnderRetracts := sorry

end Left

namespace IsRightAdmissible

/-- A right-admissible object property is automatically stable under retracts. -/
instance stableUnderRetracts (A : ObjectProperty D) [IsRightAdmissible A] :
    A.IsStableUnderRetracts := sorry

end IsRightAdmissible

namespace IsLeftAdmissible

/-- A left-admissible object property is automatically stable under retracts. -/
instance stableUnderRetracts (A : ObjectProperty D) [IsLeftAdmissible A] :
    A.IsStableUnderRetracts := sorry

end IsLeftAdmissible

end CategoryTheory.ObjectProperty.Admissible
