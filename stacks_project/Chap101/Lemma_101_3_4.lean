/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Diagonal.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Diagonal.Representable
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
  (AlgebraicGeometry.Groupoids.Hom.relativelyRepresentable_diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
      relativelyRepresentableByAlgebraicSpaces f →
        FiberedCategoryOver.Groupoids.relativelyRepresentable
          (Hom.diagonal.{u + 1, u, u + 1} f))

/- Lemma 101.3.4 (2): let `f : X ⟶ Y` be a morphism of algebraic stacks
representable by algebraic spaces. Then the relative 2-diagonal
`Hom.diagonal f : X ⟶ X ×_Y X` is locally of finite type. -/
@[stacks 04YQ] #check
  (AlgebraicGeometry.Groupoids.Hom.LocallyOfFiniteType.diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      LocallyOfFiniteType (Hom.diagonal.{u + 1, u, u + 1} f))

/- Lemma 101.3.4 (3): let `f : X ⟶ Y` be a morphism of algebraic stacks
representable by algebraic spaces. Then the relative 2-diagonal
`Hom.diagonal f : X ⟶ X ×_Y X` is a monomorphism. -/
@[stacks 04YQ] #check
  (AlgebraicGeometry.Groupoids.Hom.Mono.diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
      relativelyRepresentableByAlgebraicSpaces f →
        AlgebraicGeometry.Groupoids.Hom.Mono
          (Hom.diagonal.{u + 1, u, u + 1} f))

/- Lemma 101.3.4 (4): let `f : X ⟶ Y` be a morphism of algebraic stacks
representable by algebraic spaces. Then the relative 2-diagonal
`Hom.diagonal f : X ⟶ X ×_Y X` is separated. -/
@[stacks 04YQ] #check
  (AlgebraicGeometry.Groupoids.Hom.has_separated_diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
      relativelyRepresentableByAlgebraicSpaces f →
        has (@AlgebraicSpace.Separated S)
          (Hom.diagonal.{u + 1, u, u + 1} f))

/- Lemma 101.3.4 (5): let `f : X ⟶ Y` be a morphism of algebraic stacks
representable by algebraic spaces. Then the relative 2-diagonal
`Hom.diagonal f : X ⟶ X ×_Y X` is locally quasi-finite. -/
@[stacks 04YQ] #check
  (AlgebraicGeometry.Groupoids.Hom.has_locallyQuasiFinite_diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
      relativelyRepresentableByAlgebraicSpaces f →
        has (@AlgebraicSpace.LocallyQuasiFinite S)
          (Hom.diagonal.{u + 1, u, u + 1} f))
