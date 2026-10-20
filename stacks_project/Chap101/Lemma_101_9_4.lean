module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Morphism.Affine.Diagonal
import StacksCheckRecall

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

/- Lemma 101.9.4: let `f : X ⟶ Y` and `b : Y ⟶ Z` be morphisms of algebraic
stacks. If `a := f ≫ b` is affine and the relative diagonal
`Hom.diagonal b` is affine, then `f` is affine. The commutative triangle is
presented by its composite `a := f ≫ b`. -/
@[stacks 0GQE] #check
  (AlgebraicGeometry.Groupoids.Hom.Affine.of_comp_of_affineDiagonal :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (b : Y ⟶ Z) [Affine (f ≫ b)]
      [Affine (diagonal.{u + 1, u, u + 1} b)],
      Affine f)

end Affine
end AlgebraicGeometry.Groupoids.Hom
