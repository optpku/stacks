/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Lemma_100_8_4
import StacksCheckRecall

/-!
# First and second diagonals of morphisms of algebraic stacks

A morphism of algebraic stacks is a monomorphism if and only if its first
diagonal is an isomorphism of stacks, and is representable by algebraic
spaces if and only if that first diagonal is a monomorphism. The second
diagonal is always a monomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

/- Lemma 101.6.3 (1): a morphism `f : X ⟶ Y` of algebraic stacks is a
monomorphism if and only if the first diagonal `Hom.diagonal f` is an
isomorphism of stacks. -/
@[stacks 0AHJ] #check
  (Mono.iff_diagonal_isEquivalence :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      Groupoids.Hom.Mono f ↔
        BasedFunctor.IsEquivalence
          (toBasedFunctor (Hom.diagonal.{u + 1, u, u + 1} f)))

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.6.3 (2): a morphism `f : X ⟶ Y` of algebraic stacks is
representable by algebraic spaces if and only if the first diagonal
`Hom.diagonal f` is a monomorphism. -/
@[stacks 0AHJ]
theorem relativelyRepresentableByAlgebraicSpaces_iff_mono_diagonal
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    relativelyRepresentableByAlgebraicSpaces f ↔
      Groupoids.Hom.Mono (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

/-- A morphism of algebraic stacks whose first diagonal is a monomorphism is
representable by algebraic spaces. -/
theorem relativelyRepresentableByAlgebraicSpaces_of_mono_diagonal
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] {f : X ⟶ Y}
    [Groupoids.Hom.Mono (Hom.diagonal.{u + 1, u, u + 1} f)] :
    relativelyRepresentableByAlgebraicSpaces f :=
  sorry

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.Groupoids.Hom
namespace Mono

/-- Lemma 101.6.3 (3): the second diagonal
`Hom.diagonal (Hom.diagonal f)` of a morphism of algebraic stacks is always
a monomorphism. -/
@[stacks 0AHJ]
instance secondDiagonal {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} :
    Mono (Hom.diagonal.{u + 1, u, u + 1}
      (Hom.diagonal.{u + 1, u, u + 1} f)) :=
  sorry

end Mono
end AlgebraicGeometry.Groupoids.Hom
