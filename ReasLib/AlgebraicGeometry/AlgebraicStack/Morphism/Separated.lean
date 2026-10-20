module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Separated representable morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces is separated
in the scheme-slice sense of algebraic spaces if and only if its relative
2-diagonal is a closed immersion, equivalently proper, equivalently
universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A morphism of algebraic stacks representable by algebraic spaces is
separated if and only if its relative 2-diagonal is a closed immersion,
equivalently proper, equivalently universally closed. -/
@[stacks 04YS]
theorem separated_tfae {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    List.TFAE
      [has (@AlgebraicSpace.Separated S) f,
        has (@AlgebraicSpace.IsClosedImmersion S)
          (Hom.diagonal.{u + 1, u, u + 1} f),
        has (@AlgebraicSpace.Proper S) (Hom.diagonal.{u + 1, u, u + 1} f),
        has (@AlgebraicSpace.UniversallyClosed S)
          (Hom.diagonal.{u + 1, u, u + 1} f)] :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces is
separated on scheme-slice tests if and only if its relative 2-diagonal is a
closed immersion. -/
theorem has_separated_iff_closedImmersion_diagonal {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.Separated S) f ↔
      has (@AlgebraicSpace.IsClosedImmersion S)
        (Hom.diagonal.{u + 1, u, u + 1} f) :=
  (separated_tfae hf).out 0 1

/-- A morphism of algebraic stacks representable by algebraic spaces is
separated on scheme-slice tests if and only if its relative 2-diagonal is
proper. -/
theorem has_separated_iff_proper_diagonal {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.Separated S) f ↔
      has (@AlgebraicSpace.Proper S) (Hom.diagonal.{u + 1, u, u + 1} f) :=
  (separated_tfae hf).out 0 2

/-- A morphism of algebraic stacks representable by algebraic spaces is
separated on scheme-slice tests if and only if its relative 2-diagonal is
universally closed. -/
theorem has_separated_iff_universallyClosed_diagonal {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.Separated S) f ↔
      has (@AlgebraicSpace.UniversallyClosed S)
        (Hom.diagonal.{u + 1, u, u + 1} f) :=
  (separated_tfae hf).out 0 3

end AlgebraicGeometry.Groupoids.Hom
