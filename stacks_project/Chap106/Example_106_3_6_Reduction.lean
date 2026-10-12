/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_10_4_Reduced
public import stacks_project.Chap100.Lemma_100_9_10_Substack
public import stacks_project.Chap106.Definition_106_3_1_Thickening
public import stacks_project.Chap106.Lemma_106_3_5_Composition

/-!
# Reduction inclusions as thickenings of algebraic stacks

The canonical closed immersion from the reduction of an algebraic stack is a
thickening. A thickening of algebraic stacks identifies reduced induced closed
substacks, and presents the ambient reduction if and only if its source is
reduced.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom (ClosedImmersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The reduction inclusion of an algebraic stack is surjective on associated
point spaces. -/
instance instSurjective_reductionι {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : Surjective (reductionι X) :=
  sorry

/-- The reduction inclusion of an algebraic stack is a thickening. -/
instance instIsThickening_reductionι {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : IsThickening (reductionι X) where
  toClosedImmersion := inferInstance
  toSurjective := inferInstance

namespace IsThickening

/-- If `i : X ⟶ X'` is a thickening of algebraic stacks, the reduced induced
closed substack of `X'` agrees with the image of `reductionι X ≫ i`. -/
theorem reduction_image_eq {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    (ClosedSubstack.image (reductionι X ≫ i)).objectProperty =
      (ClosedSubstack.image (reductionι X')).objectProperty :=
  sorry

/-- A thickening `i : X ⟶ X'` presents the reduction of `X'` if and only if `X`
is reduced. -/
theorem eq_reduction_iff_isReduced {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    (ClosedSubstack.image i).objectProperty =
      (ClosedSubstack.image (reductionι X')).objectProperty ↔ IsReduced X :=
  sorry

end IsThickening

end AlgebraicGeometry.AlgebraicStack
