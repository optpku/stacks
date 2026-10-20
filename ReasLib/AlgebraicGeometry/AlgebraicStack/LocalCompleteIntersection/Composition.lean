/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocalCompleteIntersection

/-!
# Composition of local complete intersection morphisms of algebraic stacks

The composition of local complete intersection morphisms of algebraic stacks is
a local complete intersection.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace IsLocalCompleteIntersection

/-- The composition of local complete intersection morphisms of algebraic stacks
is a local complete intersection. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsLocalCompleteIntersection f] [IsLocalCompleteIntersection g] :
    IsLocalCompleteIntersection (f ≫ g) := sorry

end IsLocalCompleteIntersection

end AlgebraicGeometry.AlgebraicStack
