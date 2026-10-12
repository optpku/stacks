/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Admissible Pretriangulated Subcategories

Admissibility is a property of the canonical inclusion of a strictly full
triangulated object property.  The definitions intentionally require only the
pretriangulated ambient structure; a globally triangulated category is needed
only by stronger decomposition theorems.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory.ObjectProperty

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A strictly full triangulated subcategory is right admissible when its inclusion has a right
adjoint. -/
@[stacks 0FXD "right admissible triangulated subcategory"]
class IsRightAdmissible (A : ObjectProperty D) : Prop extends
    A.IsTriangulated, A.IsClosedUnderIsomorphisms, A.ι.IsLeftAdjoint

/-- A strictly full triangulated subcategory is left admissible when its inclusion has a left
adjoint. -/
@[stacks 0FXD "left admissible triangulated subcategory"]
class IsLeftAdmissible (A : ObjectProperty D) : Prop extends
    A.IsTriangulated, A.IsClosedUnderIsomorphisms, A.ι.IsRightAdjoint

/-- A strictly full triangulated subcategory is admissible when its inclusion has both adjoints. -/
@[stacks 0FXD]
class IsAdmissible (A : ObjectProperty D) : Prop extends
    A.IsTriangulated, A.IsClosedUnderIsomorphisms, A.ι.IsLeftAdjoint, A.ι.IsRightAdjoint

/-- Right admissibility is exactly triangulatedity and strict fullness together with a right
adjoint to the inclusion. -/
theorem isRightAdmissible_iff (A : ObjectProperty D) :
    IsRightAdmissible A ↔
      A.IsTriangulated ∧ A.IsClosedUnderIsomorphisms ∧ A.ι.IsLeftAdjoint := sorry

/-- Left admissibility is exactly triangulatedity and strict fullness together with a left
adjoint to the inclusion. -/
theorem isLeftAdmissible_iff (A : ObjectProperty D) :
    IsLeftAdmissible A ↔
      A.IsTriangulated ∧ A.IsClosedUnderIsomorphisms ∧ A.ι.IsRightAdjoint := sorry

/-- Two-sided admissibility is exactly triangulatedity and strict fullness together with both
adjoints to the inclusion. -/
theorem isAdmissible_iff (A : ObjectProperty D) :
    IsAdmissible A ↔
      A.IsTriangulated ∧ A.IsClosedUnderIsomorphisms ∧ A.ι.IsLeftAdjoint ∧ A.ι.IsRightAdjoint := sorry

namespace IsAdmissible

/-- Two-sided admissibility supplies right admissibility. -/
instance isRight (A : ObjectProperty D) [IsAdmissible A] :
    IsRightAdmissible A := sorry

/-- Two-sided admissibility supplies left admissibility. -/
instance isLeft (A : ObjectProperty D) [IsAdmissible A] :
    IsLeftAdmissible A := sorry

end IsAdmissible

end

end CategoryTheory.ObjectProperty
