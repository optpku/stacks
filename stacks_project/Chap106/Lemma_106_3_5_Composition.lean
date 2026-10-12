/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap106.Definition_106_3_1_Thickening

/-!
# Composition of thickenings of algebraic stacks

The composite of two thickenings of algebraic stacks is again a thickening.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace IsThickening

/-- The composite of two thickenings of algebraic stacks is a thickening. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsThickening f] [IsThickening g] :
    IsThickening (f ≫ g) :=
  sorry

end IsThickening

end AlgebraicGeometry.AlgebraicStack
