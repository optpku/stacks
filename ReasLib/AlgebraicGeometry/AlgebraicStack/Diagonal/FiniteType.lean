/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Diagonals of morphisms of algebraic stacks

The relative 2-diagonal of a morphism of algebraic stacks is representable by
algebraic spaces and locally of finite type in the scheme-slice sense.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- The relative 2-diagonal of a morphism of algebraic stacks is representable
by algebraic spaces. -/
theorem relativelyRepresentableByAlgebraicSpaces_diagonal
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    relativelyRepresentableByAlgebraicSpaces
      (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

namespace LocallyOfFiniteType

/-- The relative 2-diagonal of a morphism of algebraic stacks is locally of
finite type in the scheme-slice sense of representable morphisms. -/
instance diagonal {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    LocallyOfFiniteType (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end LocallyOfFiniteType

/-- The relative 2-diagonal of a morphism of algebraic stacks has the
scheme-slice locally-of-finite-type property of algebraic spaces. -/
theorem has_locallyOfFiniteType_diagonal {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    has (@AlgebraicSpace.LocallyOfFiniteType S)
      (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
