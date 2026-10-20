/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.Spectral.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiSeparated

/-!
# Spectral spaces of algebraic-stack points

The space of points of a quasi-compact algebraic stack with quasi-compact
absolute diagonal is spectral. Without global quasi-compactness, the space
admits an open covering by spectral subspaces and is sober.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open TopologicalSpace
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The space of points of a quasi-compact algebraic stack whose absolute diagonal
is quasi-compact is a spectral topological space. -/
@[stacks 0DQN]
theorem spectralSpace_of_quasiCompact_diagonal {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiCompact X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))) :
    SpectralSpace (Points X) :=
  sorry

/-- The space of points of a quasi-compact and quasi-separated algebraic stack
is a spectral topological space. -/
@[stacks 0DQP]
instance instSpectralSpacePoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X] :
    SpectralSpace (Points X) :=
  spectralSpace_of_quasiCompact_diagonal X (IsQuasiSeparated.quasiCompact_diagonal (X := X))

/-- The space of points of an algebraic stack with quasi-compact absolute diagonal
admits an open covering by spectral subspaces. -/
@[stacks 0DQQ]
theorem exists_isOpenCover_spectral_of_quasiCompact_diagonal {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))) :
    ∃ (ι : Type (u + 1)) (U : ι → Opens (Points X)),
      IsOpenCover U ∧ ∀ i, SpectralSpace (U i) :=
  sorry

/-- The space of points of an algebraic stack with quasi-compact absolute diagonal
is sober. -/
@[stacks 0DQQ]
theorem sober_of_quasiCompact_diagonal {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))) :
    T0Space (Points X) ∧ QuasiSober (Points X) :=
  sorry

/-- Every irreducible closed subset of the space of points of an algebraic stack
with quasi-compact absolute diagonal has a unique generic point. -/
theorem existsUnique_isGenericPoint_of_quasiCompact_diagonal {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X)))
    {T : Set (Points X)} (hT_irred : IsIrreducible T) (hT_closed : IsClosed T) :
    ∃! x : Points X, IsGenericPoint x T :=
  sorry

namespace IsQuasiSeparated

/-- The space of points of a quasi-separated algebraic stack admits an open
covering by spectral subspaces. -/
theorem exists_isOpenCover_spectral {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiSeparated X] :
    ∃ (ι : Type (u + 1)) (U : ι → Opens (Points X)),
      IsOpenCover U ∧ ∀ i, SpectralSpace (U i) :=
  sorry

/-- The space of points of a quasi-separated algebraic stack is Kolmogorov. -/
instance instT0SpacePoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiSeparated X] : T0Space (Points X) :=
  sorry

/-- The space of points of a quasi-separated algebraic stack is quasi-sober. -/
instance instQuasiSoberPoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiSeparated X] : QuasiSober (Points X) :=
  sorry

end IsQuasiSeparated

end AlgebraicGeometry.AlgebraicStack
