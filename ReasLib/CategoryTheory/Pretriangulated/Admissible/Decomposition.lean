/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.Admissible
public import ReasLib.CategoryTheory.Pretriangulated.Extension
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Admissible Subcategories and Semiorthogonal Decompositions

The canonical partial-adjoint domains of a full subcategory inclusion are
semiorthogonal extension products.  Keeping these equalities separate from
adjoint existence lets downstream arguments work objectwise before asking for
a global adjoint.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

universe v u

namespace CategoryTheory.ObjectProperty.Admissible

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (A : ObjectProperty D) [A.IsTriangulated]

namespace Right

/-- Stacks 0CQS: the domain of the partial right adjoint to the inclusion of
`A` is the extension product of `A` with its right orthogonal. -/
@[stacks 0CQS]
theorem domain_eq :
    A.ι.rightAdjointObjIsDefined = A ⋆ A.rightOrthogonal := sorry

/-- Stacks 0CQS: the inclusion of `A` has a right adjoint exactly when the
semiorthogonal extension product `A ⋆ A.rightOrthogonal` contains every object. -/
@[stacks 0CQS]
theorem isLeftAdjoint_iff :
    A.ι.IsLeftAdjoint ↔ A ⋆ A.rightOrthogonal = ⊤ := sorry

end Right

namespace Left

/-- Stacks 0CQT: the domain of the partial left adjoint to the inclusion of
`A` is the extension product of its left orthogonal with `A`. -/
@[stacks 0CQT]
theorem domain_eq :
    A.ι.leftAdjointObjIsDefined = A.leftOrthogonal ⋆ A := sorry

/-- Stacks 0CQT: the inclusion of `A` has a left adjoint exactly when the
semiorthogonal extension product `A.leftOrthogonal ⋆ A` contains every object. -/
@[stacks 0CQT]
theorem isRightAdjoint_iff :
    A.ι.IsRightAdjoint ↔ A.leftOrthogonal ⋆ A = ⊤ := sorry

end Left

end CategoryTheory.ObjectProperty.Admissible
