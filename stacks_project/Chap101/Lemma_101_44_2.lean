/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_44_4_LocalCompleteIntersection

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

/-- Lemma 101.44.2: The composition of local complete intersection morphisms is
a local complete intersection. -/
@[stacks 0CJ4]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsLocalCompleteIntersection f] [IsLocalCompleteIntersection g] :
    IsLocalCompleteIntersection (f ≫ g) :=
  sorry

end IsLocalCompleteIntersection

end AlgebraicGeometry.AlgebraicStack
