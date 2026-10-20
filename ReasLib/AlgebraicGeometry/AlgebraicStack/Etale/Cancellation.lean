/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale.Isomorphism

/-!
# Cancellation of étaleness against étale postcomposition

If a composite morphism of algebraic stacks is étale and the second factor is
étale, then the first factor is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Etale

/-- If a composite morphism of algebraic stacks is étale and the second factor
is étale, then the first factor is étale. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [Etale (f ≫ g)] [Etale g] : Etale f := sorry

/-- Étaleness of `f : X ⟶ Y` follows from étaleness of a 2-isomorphic
hypotenuse `p ≅ f ≫ q` and of `q`. -/
theorem of_two_commute {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (α : p ≅ f ≫ q)
    [Etale p] [Etale q] : Etale f := sorry

end AlgebraicGeometry.AlgebraicStack.Etale
