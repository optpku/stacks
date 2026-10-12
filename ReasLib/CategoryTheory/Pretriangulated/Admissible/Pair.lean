/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.Admissible.Orthogonal
public import ReasLib.CategoryTheory.Pretriangulated.Subcategory.Orthogonal
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Admissible Semiorthogonal Pairs

This leaf records the symmetric interface between one-sided admissibility and
a semiorthogonal decomposition by a pair of object properties.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

universe v u

namespace CategoryTheory.ObjectProperty.Admissible.Pair

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- If `A ⋆ B` contains every object and `B` is right-orthogonal to `A`, then
`B` contains the whole right orthogonal of `A`. -/
theorem rightOrthogonal_le (A B : ObjectProperty D)
    [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    [B.IsClosedUnderIsomorphisms]
    (horth : B ≤ A.rightOrthogonal) (htop : A ⋆ B = ⊤) :
    A.rightOrthogonal ≤ B := sorry

/-- If `A ⋆ B` contains every object and `B` is right-orthogonal to `A`, then
`A` contains the whole left orthogonal of `B`. -/
theorem leftOrthogonal_le (A B : ObjectProperty D)
    [B.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    (horth : B ≤ A.rightOrthogonal) (htop : A ⋆ B = ⊤) :
    B.leftOrthogonal ≤ A := sorry

/-- A semiorthogonal decomposition identifies its right term with the right
orthogonal of its left term. -/
theorem eq_rightOrthogonal (A B : ObjectProperty D)
    [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    [B.IsClosedUnderIsomorphisms]
    (horth : B ≤ A.rightOrthogonal) (htop : A ⋆ B = ⊤) :
    B = A.rightOrthogonal := sorry

/-- A semiorthogonal decomposition identifies its left term with the left
orthogonal of its right term. -/
theorem eq_leftOrthogonal (A B : ObjectProperty D)
    [B.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    (horth : B ≤ A.rightOrthogonal) (htop : A ⋆ B = ⊤) :
    A = B.leftOrthogonal := sorry

/-- Stacks 0H0P: right admissibility of `A`, left admissibility of `B`, and a
semiorthogonal decomposition by `A` and `B` are equivalent descriptions. -/
@[stacks 0H0P]
theorem tfae (A B : ObjectProperty D) :
    List.TFAE
      [ IsRightAdmissible A ∧ B = A.rightOrthogonal
      , IsLeftAdmissible B ∧ A = B.leftOrthogonal
      , A.IsTriangulated ∧ A.IsClosedUnderIsomorphisms ∧
          B.IsTriangulated ∧ B.IsClosedUnderIsomorphisms ∧
          B ≤ A.rightOrthogonal ∧ A ⋆ B = ⊤ ] := sorry

end CategoryTheory.ObjectProperty.Admissible.Pair
