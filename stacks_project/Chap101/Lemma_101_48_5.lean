/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_28_1_Gerbe
public import stacks_project.Chap101.Definition_101_50_1_Decent

/-!
# Descent of decency along gerbes

If `f : X ⟶ Y` is a gerbe morphism of algebraic stacks and `X` is decent, then
`Y` is decent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.48.5: Let `f : X ⟶ Y` be a morphism of algebraic stacks. If `X`
is a gerbe over `Y` and `X` is decent, then `Y` is decent. -/
@[stacks 0GW5]
theorem IsDecent.of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f]
    [IsDecent X] : IsDecent Y :=
  sorry

end AlgebraicGeometry.AlgebraicStack
