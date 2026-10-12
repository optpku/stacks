/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_39_12_Existence

/-!
# Composition of the existence part of the valuative criterion

The composition of morphisms of algebraic stacks which satisfy the existence
part of the valuative criterion again satisfies the existence part of the
valuative criterion.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack
namespace ValuativeCriterion

/-- Lemma 101.39.12: The composition of morphisms of algebraic stacks which
satisfy the existence part of the valuative criterion is another morphism of
algebraic stacks which satisfies the existence part of the valuative
criterion. -/
@[stacks 0CLM]
instance Existence.comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Existence f] [Existence g] :
    Existence (f ≫ g) :=
  sorry

end ValuativeCriterion
end AlgebraicGeometry.AlgebraicStack
