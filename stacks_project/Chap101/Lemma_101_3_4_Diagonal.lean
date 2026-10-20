/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Diagonal.Representable

/-!
# Diagonals of representable morphisms of algebraic stacks

If a morphism of algebraic stacks is representable by algebraic spaces, then
its relative 2-diagonal is representable by schemes, a monomorphism, separated,
and locally quasi-finite in the scheme-slice sense.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

#check
  (AlgebraicGeometry.Groupoids.Hom.relativelyRepresentable_diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
      relativelyRepresentableByAlgebraicSpaces f →
        FiberedCategoryOver.Groupoids.relativelyRepresentable
          (Hom.diagonal.{u + 1, u, u + 1} f))

#check
  (AlgebraicGeometry.Groupoids.Hom.Mono.diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
      relativelyRepresentableByAlgebraicSpaces f →
        AlgebraicGeometry.Groupoids.Hom.Mono
          (Hom.diagonal.{u + 1, u, u + 1} f))

#check
  (AlgebraicGeometry.Groupoids.Hom.has_separated_diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
      relativelyRepresentableByAlgebraicSpaces f →
        has (@AlgebraicSpace.Separated S)
          (Hom.diagonal.{u + 1, u, u + 1} f))

#check
  (AlgebraicGeometry.Groupoids.Hom.has_locallyQuasiFinite_diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
      relativelyRepresentableByAlgebraicSpaces f →
        has (@AlgebraicSpace.LocallyQuasiFinite S)
          (Hom.diagonal.{u + 1, u, u + 1} f))
