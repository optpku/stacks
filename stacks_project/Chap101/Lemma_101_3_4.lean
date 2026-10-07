module

public import stacks_project.Chap101.Lemma_101_3_3_Diagonal
public import stacks_project.Chap101.Lemma_101_3_4_Diagonal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 101.3.4 (1): let `f : X ⟶ Y` be a morphism of algebraic stacks
representable by algebraic spaces. Then the relative 2-diagonal
`Hom.diagonal f : X ⟶ X ×_Y X` is representable by schemes. -/
@[stacks 04YQ] #check
  (relativelyRepresentable_diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
      relativelyRepresentableByAlgebraicSpaces f →
        FiberedCategoryOver.Groupoids.relativelyRepresentable
          (Hom.diagonal.{u + 1, u, u + 1} f))

/- Lemma 101.3.4 (2): let `f : X ⟶ Y` be a morphism of algebraic stacks
representable by algebraic spaces. Then the relative 2-diagonal
`Hom.diagonal f : X ⟶ X ×_Y X` is locally of finite type. -/
@[stacks 04YQ] #check
  (LocallyOfFiniteType.diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      LocallyOfFiniteType (Hom.diagonal.{u + 1, u, u + 1} f))

/- Lemma 101.3.4 (3): let `f : X ⟶ Y` be a morphism of algebraic stacks
representable by algebraic spaces. Then the relative 2-diagonal
`Hom.diagonal f : X ⟶ X ×_Y X` is a monomorphism. -/
@[stacks 04YQ] #check
  (Mono.diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
      relativelyRepresentableByAlgebraicSpaces f →
        AlgebraicGeometry.Groupoids.Hom.Mono
          (Hom.diagonal.{u + 1, u, u + 1} f))

/- Lemma 101.3.4 (4): let `f : X ⟶ Y` be a morphism of algebraic stacks
representable by algebraic spaces. Then the relative 2-diagonal
`Hom.diagonal f : X ⟶ X ×_Y X` is separated. -/
@[stacks 04YQ] #check
  (has_separated_diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
      relativelyRepresentableByAlgebraicSpaces f →
        has (@AlgebraicSpace.Separated S)
          (Hom.diagonal.{u + 1, u, u + 1} f))

/- Lemma 101.3.4 (5): let `f : X ⟶ Y` be a morphism of algebraic stacks
representable by algebraic spaces. Then the relative 2-diagonal
`Hom.diagonal f : X ⟶ X ×_Y X` is locally quasi-finite. -/
@[stacks 04YQ] #check
  (has_locallyQuasiFinite_diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
      relativelyRepresentableByAlgebraicSpaces f →
        has (@AlgebraicSpace.LocallyQuasiFinite S)
          (Hom.diagonal.{u + 1, u, u + 1} f))
