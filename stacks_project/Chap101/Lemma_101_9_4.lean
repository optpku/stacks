/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap101.Definition_101_9_1_Affine

/-!
# Affine permanence for morphisms of algebraic stacks

In a commutative triangle of morphisms of algebraic stacks, an affine first
leg may be cancelled when the second leg has affine relative 2-diagonal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.Hom (diagonal)
open scoped Bicategory

universe u

noncomputable section

namespace AlgebraicGeometry.Groupoids.Hom
namespace Affine

/-- Lemma 101.9.4: let `f : X ⟶ Y` and `b : Y ⟶ Z` be morphisms of algebraic
stacks. If `a := f ≫ b` is affine and the relative diagonal
`Hom.diagonal b` is affine, then `f` is affine. -/
@[stacks 0GQE]
theorem of_comp_of_affineDiagonal {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (b : Y ⟶ Z) [Affine (f ≫ b)]
    [Affine (diagonal.{u + 1, u, u + 1} b)] :
    Affine f :=
  sorry

end Affine
end AlgebraicGeometry.Groupoids.Hom
