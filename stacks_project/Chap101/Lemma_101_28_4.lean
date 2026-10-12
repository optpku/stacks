/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_28_1_Gerbe

/-!
# Composition of gerbes of algebraic stacks

If `X ⟶ Y` and `Y ⟶ Z` are morphisms of algebraic stacks, `X` is a gerbe over
`Y`, and `Y` is a gerbe over `Z`, then `X` is a gerbe over `Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Gerbe

/-- Lemma 101.28.4: Let `X ⟶ Y` and `Y ⟶ Z` be morphisms of algebraic stacks.
If `X` is a gerbe over `Y` and `Y` is a gerbe over `Z`, then `X` is a gerbe
over `Z`. -/
@[stacks 06R8]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Gerbe f] [Gerbe g] :
    Gerbe (f ≫ g) :=
  sorry

end Gerbe

end AlgebraicGeometry.AlgebraicStack
