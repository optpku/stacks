module

public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.Spectral.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap100.Lemma_100_4_7_Topology
public import stacks_project.Chap101.Definition_101_8_1_Noetherian

/-!
# Open spectral coverings of algebraic stacks with quasi-compact diagonal

An algebraic stack whose absolute diagonal is quasi-compact has an open covering
of its space of points by spectral spaces, and in particular that space is sober.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open TopologicalSpace
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.30.3 (1): Let `X` be an algebraic stack whose diagonal is quasi-compact.
Then there is an open covering `|X| = ⋃ i, U i` with each `U i` spectral. -/
@[stacks 0DQQ]
theorem exists_isOpenCover_spectral_of_quasiCompact_diagonal {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))) :
    ∃ (ι : Type (u + 1)) (U : ι → Opens (Points X)),
      IsOpenCover U ∧ ∀ i, SpectralSpace (U i) :=
  sorry

/-- Lemma 101.30.3 (2): In particular, if `X` is an algebraic stack whose diagonal is
quasi-compact, then `|X|` is a sober topological space. -/
@[stacks 0DQQ]
theorem sober_of_quasiCompact_diagonal {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))) :
    T0Space (Points X) ∧ QuasiSober (Points X) :=
  sorry

/-- Every irreducible closed subset of `Points X` has a unique generic point when the
absolute diagonal of `X` is quasi-compact. -/
theorem existsUnique_isGenericPoint_of_quasiCompact_diagonal {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X)))
    {T : Set (Points X)} (hT_irred : IsIrreducible T) (hT_closed : IsClosed T) :
    ∃! x : Points X, IsGenericPoint x T :=
  sorry

namespace IsQuasiSeparated

/-- A quasi-separated algebraic stack admits an open covering of `|X|` by spectral
spaces. -/
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
