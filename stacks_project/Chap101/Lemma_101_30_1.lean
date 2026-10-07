module

public import Mathlib.Topology.Spectral.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap100.Lemma_100_4_7_Topology
public import stacks_project.Chap101.Definition_101_8_1_Noetherian

/-!
# Spectral spaces of quasi-compact algebraic stacks with quasi-compact diagonal

A quasi-compact algebraic stack whose absolute diagonal is quasi-compact has
spectral space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.30.1: Let `X` be a quasi-compact algebraic stack whose diagonal `Δ`
is quasi-compact. Then `|X|` is a spectral topological space. -/
@[stacks 0DQN]
theorem spectralSpace_of_quasiCompact_diagonal {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiCompact X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))) :
    SpectralSpace (Points X) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
