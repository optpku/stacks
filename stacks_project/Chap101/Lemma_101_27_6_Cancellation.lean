/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType

/-!
# Cancellation of local finite presentation against locally finite type postcomposition

If a composite morphism of algebraic stacks is locally of finite presentation and
the second factor is locally of finite type, then the first factor is locally of
finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-- If a composite morphism of algebraic stacks is locally of finite presentation
and the second factor is locally of finite type, then the first factor is
locally of finite presentation. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f := sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
