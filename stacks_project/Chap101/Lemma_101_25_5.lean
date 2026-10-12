/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap101.Lemma_101_25_5_Surjective

/-!
# Permanence of flatness for morphisms of algebraic stacks

If `X ⟶ Z` is flat and `X ⟶ Y` is surjective and flat, then `Y ⟶ Z` is
flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Flat

/-- Lemma 101.25.5: Let `X ⟶ Y ⟶ Z` be morphisms of algebraic stacks. If
`X ⟶ Z` is flat and `X ⟶ Y` is surjective and flat, then `Y ⟶ Z` is
flat. -/
@[stacks 06Q0]
theorem of_comp_surjective_flat {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicStack.Flat (f ≫ g)] [AlgebraicStack.Flat f]
    [AlgebraicStack.Surjective f] : AlgebraicStack.Flat g :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Flat
