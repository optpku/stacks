module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Locally separated representable morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces is locally
separated in the scheme-slice sense of algebraic spaces if and only if its
relative 2-diagonal is an immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A morphism of algebraic stacks representable by algebraic spaces is
locally separated if and only if its relative 2-diagonal is an immersion. -/
@[stacks 04YU]
theorem locallySeparated_tfae {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    List.TFAE
      [has (@AlgebraicSpace.LocallySeparated S) f,
        has (@AlgebraicSpace.IsImmersion S)
          (Hom.diagonal.{u + 1, u, u + 1} f)] :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces is
locally separated on scheme-slice tests if and only if its relative 2-diagonal
is an immersion. -/
theorem has_locallySeparated_iff_immersion_diagonal {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.LocallySeparated S) f ↔
      has (@AlgebraicSpace.IsImmersion S)
        (Hom.diagonal.{u + 1, u, u + 1} f) :=
  (locallySeparated_tfae hf).out 0 1

end AlgebraicGeometry.Groupoids.Hom
