module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Diagonal.Monomorphism
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
  (AlgebraicGeometry.Groupoids.Hom.Mono.iff_diagonal_isEquivalence :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      Groupoids.Hom.Mono f ↔
        BasedFunctor.IsEquivalence
          (toBasedFunctor (Hom.diagonal.{u + 1, u, u + 1} f)))

/- Lemma 101.6.3 (2): a morphism `f : X ⟶ Y` of algebraic stacks is
representable by algebraic spaces if and only if the first diagonal
`Hom.diagonal f` is a monomorphism. -/
@[stacks 0AHJ] #check
  (AlgebraicGeometry.AlgebraicStack.relativelyRepresentableByAlgebraicSpaces_iff_mono_diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      relativelyRepresentableByAlgebraicSpaces f ↔
        Groupoids.Hom.Mono (Hom.diagonal.{u + 1, u, u + 1} f))

/- Lemma 101.6.3 (3): the second diagonal
`Hom.diagonal (Hom.diagonal f)` of a morphism of algebraic stacks is always
a monomorphism. -/
@[stacks 0AHJ] #check
  (AlgebraicGeometry.Groupoids.Hom.Mono.secondDiagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
      Groupoids.Hom.Mono (Hom.diagonal.{u + 1, u, u + 1}
        (Hom.diagonal.{u + 1, u, u + 1} f)))
