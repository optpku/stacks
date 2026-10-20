/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective

/-!
# Cancellation of universal closedness

Universal closedness of a composite of morphisms of algebraic stacks cancels
through a separated second factor or a surjective first factor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.UniversallyClosed

/-- If a composite morphism of algebraic stacks is universally closed and the
second factor is separated, then the first factor is universally closed. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [UniversallyClosed (f ≫ g)] [Separated g] : UniversallyClosed f :=
  sorry

/-- If a composite morphism of algebraic stacks is universally closed and the
first factor is surjective, then the second factor is universally closed. -/
@[stacks 0CQK]
theorem of_comp_surjective {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyClosed (f ≫ g)] [Surjective f] :
    UniversallyClosed g :=
  sorry

end AlgebraicGeometry.AlgebraicStack.UniversallyClosed
