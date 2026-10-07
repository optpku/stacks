module

public import stacks_project.Chap106.Example_106_3_6_Reduction
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Example 106.3.6 (1): if `X'` is an algebraic stack, then `X'` is a thickening
of its reduction, recovered as `IsThickening (reductionι X')`. -/
@[stacks 0BPT] #check
  (instIsThickening_reductionι : ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X], IsThickening (reductionι X))

/- Example 106.3.6 (2): if `i : X ⟶ X'` is a thickening of algebraic stacks,
then the reduced induced closed substacks agree after viewing the reduction of
`X` inside `X'` via `reductionι X ≫ i`. -/
@[stacks 0BPT] #check
  (IsThickening.reduction_image_eq : ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i],
    (ClosedSubstack.image (reductionι X ≫ i)).objectProperty =
      (ClosedSubstack.image (reductionι X')).objectProperty)

/- Example 106.3.6 (3): equivalently, a thickening `i : X ⟶ X'` presents the
reduction of `X'` if and only if `X` is reduced. -/
@[stacks 0BPT] #check
  (IsThickening.eq_reduction_iff_isReduced :
    ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i],
      (ClosedSubstack.image i).objectProperty =
        (ClosedSubstack.image (reductionι X')).objectProperty ↔ IsReduced X)
