/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening

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
  Surjective.of (reduction_spec X).2.2

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
    (FiberedCategoryOver.Groupoids.toFunctor (reductionι X ≫ i)).essImage =
      (FiberedCategoryOver.Groupoids.toFunctor (reductionι X')).essImage :=
  sorry

/-- A thickening `i : X ⟶ X'` presents the reduction of `X'` if and only if `X`
is reduced. -/
theorem eq_reduction_iff_isReduced {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    (FiberedCategoryOver.Groupoids.toFunctor i).essImage =
      (FiberedCategoryOver.Groupoids.toFunctor (reductionι X')).essImage ↔ IsReduced X :=
  sorry

end IsThickening

end AlgebraicGeometry.AlgebraicStack
