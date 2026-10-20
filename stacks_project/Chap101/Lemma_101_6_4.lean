/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Diagonal.Separation
import StacksCheckRecall

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

/- Lemma 101.6.4 (1): Separation of the first diagonal is equivalent to the second diagonal
being a closed immersion, proper, or universally closed. -/
@[stacks 04YZ]
#check (AlgebraicGeometry.Groupoids.Hom.firstDiagonal_separated_tfae :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    List.TFAE
      [has (@AlgebraicSpace.Separated S)
          (Hom.diagonal.{u + 1, u, u + 1} f),
        has (@AlgebraicSpace.IsClosedImmersion S)
          (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)),
        has (@AlgebraicSpace.Proper S)
          (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)),
        has (@AlgebraicSpace.UniversallyClosed S)
          (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f))])

#check (AlgebraicGeometry.Groupoids.Hom.firstDiagonal_separated_iff_secondDiagonal_closedImmersion :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y),
    has (@AlgebraicSpace.Separated S) (Hom.diagonal.{u + 1, u, u + 1} f) ↔
      has (@AlgebraicSpace.IsClosedImmersion S)
        (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)))

#check (AlgebraicGeometry.Groupoids.Hom.firstDiagonal_separated_iff_secondDiagonal_proper :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y),
    has (@AlgebraicSpace.Separated S) (Hom.diagonal.{u + 1, u, u + 1} f) ↔
      has (@AlgebraicSpace.Proper S)
        (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)))

#check (AlgebraicGeometry.Groupoids.Hom.firstDiagonal_separated_iff_secondDiagonal_universallyClosed :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y),
    has (@AlgebraicSpace.Separated S) (Hom.diagonal.{u + 1, u, u + 1} f) ↔
      has (@AlgebraicSpace.UniversallyClosed S)
        (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)))

/- Lemma 101.6.4 (2): Quasi-separatedness of the first diagonal is equivalent to the second
diagonal being of finite type or quasi-compact. -/
@[stacks 04YZ]
#check (AlgebraicGeometry.Groupoids.Hom.firstDiagonal_quasiSeparated_tfae :
    ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y),
    List.TFAE
      [has (@AlgebraicSpace.QuasiSeparated S)
          (Hom.diagonal.{u + 1, u, u + 1} f),
        has (@AlgebraicSpace.FiniteType S)
          (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)),
        has (@AlgebraicSpace.QuasiCompact S)
          (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f))])

#check (AlgebraicGeometry.Groupoids.Hom.firstDiagonal_quasiSeparated_iff_secondDiagonal_finiteType :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y),
    has (@AlgebraicSpace.QuasiSeparated S)
        (Hom.diagonal.{u + 1, u, u + 1} f) ↔
      has (@AlgebraicSpace.FiniteType S)
        (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)))

#check (AlgebraicGeometry.Groupoids.Hom.firstDiagonal_quasiSeparated_iff_secondDiagonal_quasiCompact :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y),
    has (@AlgebraicSpace.QuasiSeparated S)
        (Hom.diagonal.{u + 1, u, u + 1} f) ↔
      has (@AlgebraicSpace.QuasiCompact S)
        (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)))

/- Lemma 101.6.4 (3): Local separatedness of the first diagonal is equivalent to the second
diagonal being an immersion. -/
@[stacks 04YZ]
#check (AlgebraicGeometry.Groupoids.Hom.firstDiagonal_locallySeparated_tfae :
    ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y),
    List.TFAE
      [has (@AlgebraicSpace.LocallySeparated S)
          (Hom.diagonal.{u + 1, u, u + 1} f),
        has (@AlgebraicSpace.IsImmersion S)
          (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f))])

#check (AlgebraicGeometry.Groupoids.Hom.firstDiagonal_locallySeparated_iff_secondDiagonal_immersion :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y),
    has (@AlgebraicSpace.LocallySeparated S)
        (Hom.diagonal.{u + 1, u, u + 1} f) ↔
      has (@AlgebraicSpace.IsImmersion S)
        (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)))

end AlgebraicGeometry.Groupoids.Hom
