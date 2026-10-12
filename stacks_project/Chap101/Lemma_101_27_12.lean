/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation
public import stacks_project.Chap101.Lemma_101_25_5_Surjective

/-!
# Permanence of local finite presentation for morphisms of algebraic stacks

If `X ⟶ Z` is locally of finite presentation and `X ⟶ Y` is surjective, flat,
and locally of finite presentation, then `Y ⟶ Z` is locally of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-- Lemma 101.27.12: Let `X ⟶ Y ⟶ Z` be morphisms of algebraic stacks. If
`X ⟶ Z` is locally of finite presentation and `X ⟶ Y` is surjective, flat,
and locally of finite presentation, then `Y ⟶ Z` is locally of finite
presentation. -/
@[stacks 06Q9]
theorem of_comp_of_fppf {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ g)]
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation g :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
