/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Separated
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Diagonal.QuasiSeparated
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.LocallySeparated

/-!
# First and second diagonals of morphisms of algebraic stacks

For a morphism of algebraic stacks, the first diagonal `Hom.diagonal f` is
separated, quasi-separated, or locally separated on scheme-slice tests if and
only if the second diagonal `Hom.diagonal (Hom.diagonal f)` is a closed
immersion (equivalently proper, equivalently universally closed), of finite
type (equivalently quasi-compact), or an immersion, respectively.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Let `f : X ⟶ Y` be a morphism of algebraic stacks.
Then the first diagonal `Hom.diagonal f` is separated if and only if the
second diagonal `Hom.diagonal (Hom.diagonal f)` is a closed immersion,
equivalently proper, equivalently universally closed. -/
@[stacks 04YZ]
theorem firstDiagonal_separated_tfae {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    List.TFAE
      [has (@AlgebraicSpace.Separated S)
          (Hom.diagonal.{u + 1, u, u + 1} f),
        has (@AlgebraicSpace.IsClosedImmersion S)
          (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)),
        has (@AlgebraicSpace.Proper S)
          (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)),
        has (@AlgebraicSpace.UniversallyClosed S)
          (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f))] :=
  sorry

/-- The first diagonal of a morphism of algebraic stacks is separated on
scheme-slice tests if and only if the second diagonal is a closed immersion. -/
theorem firstDiagonal_separated_iff_secondDiagonal_closedImmersion
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    has (@AlgebraicSpace.Separated S) (Hom.diagonal.{u + 1, u, u + 1} f) ↔
      has (@AlgebraicSpace.IsClosedImmersion S)
        (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)) :=
  (firstDiagonal_separated_tfae f).out 0 1

/-- The first diagonal of a morphism of algebraic stacks is separated on
scheme-slice tests if and only if the second diagonal is proper. -/
theorem firstDiagonal_separated_iff_secondDiagonal_proper
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    has (@AlgebraicSpace.Separated S) (Hom.diagonal.{u + 1, u, u + 1} f) ↔
      has (@AlgebraicSpace.Proper S)
        (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)) :=
  (firstDiagonal_separated_tfae f).out 0 2

/-- The first diagonal of a morphism of algebraic stacks is separated on
scheme-slice tests if and only if the second diagonal is universally closed. -/
theorem firstDiagonal_separated_iff_secondDiagonal_universallyClosed
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    has (@AlgebraicSpace.Separated S) (Hom.diagonal.{u + 1, u, u + 1} f) ↔
      has (@AlgebraicSpace.UniversallyClosed S)
        (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)) :=
  (firstDiagonal_separated_tfae f).out 0 3

/-- Let `f : X ⟶ Y` be a morphism of algebraic stacks.
Then the first diagonal `Hom.diagonal f` is quasi-separated if and only if the
second diagonal `Hom.diagonal (Hom.diagonal f)` is of finite type,
equivalently quasi-compact. -/
@[stacks 04YZ]
theorem firstDiagonal_quasiSeparated_tfae {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    List.TFAE
      [has (@AlgebraicSpace.QuasiSeparated S)
          (Hom.diagonal.{u + 1, u, u + 1} f),
        has (@AlgebraicSpace.FiniteType S)
          (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)),
        has (@AlgebraicSpace.QuasiCompact S)
          (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f))] :=
  sorry

/-- The first diagonal of a morphism of algebraic stacks is quasi-separated on
scheme-slice tests if and only if the second diagonal is of finite type. -/
theorem firstDiagonal_quasiSeparated_iff_secondDiagonal_finiteType
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    has (@AlgebraicSpace.QuasiSeparated S)
        (Hom.diagonal.{u + 1, u, u + 1} f) ↔
      has (@AlgebraicSpace.FiniteType S)
        (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)) :=
  (firstDiagonal_quasiSeparated_tfae f).out 0 1

/-- The first diagonal of a morphism of algebraic stacks is quasi-separated on
scheme-slice tests if and only if the second diagonal is quasi-compact. -/
theorem firstDiagonal_quasiSeparated_iff_secondDiagonal_quasiCompact
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    has (@AlgebraicSpace.QuasiSeparated S)
        (Hom.diagonal.{u + 1, u, u + 1} f) ↔
      has (@AlgebraicSpace.QuasiCompact S)
        (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)) :=
  (firstDiagonal_quasiSeparated_tfae f).out 0 2

/-- Let `f : X ⟶ Y` be a morphism of algebraic stacks.
Then the first diagonal `Hom.diagonal f` is locally separated if and only if
the second diagonal `Hom.diagonal (Hom.diagonal f)` is an immersion. -/
@[stacks 04YZ]
theorem firstDiagonal_locallySeparated_tfae {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    List.TFAE
      [has (@AlgebraicSpace.LocallySeparated S)
          (Hom.diagonal.{u + 1, u, u + 1} f),
        has (@AlgebraicSpace.IsImmersion S)
          (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f))] :=
  sorry

/-- The first diagonal of a morphism of algebraic stacks is locally separated
on scheme-slice tests if and only if the second diagonal is an immersion. -/
theorem firstDiagonal_locallySeparated_iff_secondDiagonal_immersion
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    has (@AlgebraicSpace.LocallySeparated S)
        (Hom.diagonal.{u + 1, u, u + 1} f) ↔
      has (@AlgebraicSpace.IsImmersion S)
        (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)) :=
  (firstDiagonal_locallySeparated_tfae f).out 0 1

end AlgebraicGeometry.Groupoids.Hom
