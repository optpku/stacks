/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Lemma_100_4_7_Topology
public import stacks_project.Chap101.Lemma_101_18_4_FiniteTypePoint

/-!
# Finite-type points meet every nonempty locally closed subset

Every nonempty locally closed subset of the points of an algebraic stack meets
the finite-type points, and the finite-type points of a closed subset are dense
in that subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.18.6 (1): Let `X` be an algebraic stack. Every nonempty locally
closed subset `T ⊆ Points X` meets `finiteTypePoints X`. -/
@[stacks 06G2]
theorem nonempty_inter_finiteTypePoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] {T : Set (Points X)} (hne : T.Nonempty)
    (hT : IsLocallyClosed T) :
    (T ∩ finiteTypePoints X).Nonempty :=
  sorry

/-- Lemma 101.18.6 (2): Let `X` be an algebraic stack. For any closed subset
`T ⊆ Points X`, the finite-type points of `X` in `T` are dense in `T`. -/
@[stacks 06G2]
theorem dense_finiteTypePoints_in_closed_subset {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] {T : Set (Points X)}
    (hT : IsClosed T) :
    Dense (setOf fun (x : T) ↦ (x : Points X) ∈ finiteTypePoints X) :=
  sorry

/-- The closure of the finite-type points of an algebraic stack inside a closed
subset `T` is `T`. -/
theorem closure_inter_finiteTypePoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] {T : Set (Points X)} (hT : IsClosed T) :
    closure (T ∩ finiteTypePoints X) = T :=
  sorry

end AlgebraicGeometry.AlgebraicStack
