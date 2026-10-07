module

public import stacks_project.Chap101.Lemma_101_3_3_Diagonal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 101.3.3 (1): let `f : X ⟶ Y` be a morphism of algebraic stacks. Then
the relative 2-diagonal `Hom.diagonal f : X ⟶ X ×_Y X` is representable by
algebraic spaces. -/
@[stacks 04XS] #check
  (relativelyRepresentableByAlgebraicSpaces_diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      relativelyRepresentableByAlgebraicSpaces
        (Hom.diagonal.{u + 1, u, u + 1} f))

/- Lemma 101.3.3 (2): let `f : X ⟶ Y` be a morphism of algebraic stacks. Then
the relative 2-diagonal `Hom.diagonal f : X ⟶ X ×_Y X` is locally of finite
type. -/
@[stacks 04XS] #check
  (LocallyOfFiniteType.diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      LocallyOfFiniteType (Hom.diagonal.{u + 1, u, u + 1} f))
