/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Lemma_67_25_4_FiniteTypePoint

/-!
# Finite-type points meet every nonempty locally closed subset

Every nonempty locally closed subset of the points of an algebraic space meets
the finite-type points, and the finite-type points of a closed subset are dense
in that subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.25.6 (1): Let `S` be a scheme. Let `X` be an algebraic space over
`S`. Every nonempty locally closed subset `T ⊆ Points X` meets
`finiteTypePoints X`. -/
@[stacks 06EK]
theorem nonempty_inter_finiteTypePoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    {T : Set (Points X)} (hne : T.Nonempty) (hT : IsLocallyClosed T) :
    (T ∩ finiteTypePoints X).Nonempty :=
  sorry

/-- Lemma 67.25.6 (2): Let `S` be a scheme. Let `X` be an algebraic space over
`S`. For any closed subset `T ⊆ Points X`, the finite-type points of `X` in `T`
are dense in `T`. -/
@[stacks 06EK]
theorem dense_finiteTypePoints_in_closed_subset {S : Scheme.{u}}
    (X : AlgebraicSpace S) {T : Set (Points X)} (hT : IsClosed T) :
    Dense (setOf fun (x : T) ↦ (x : Points X) ∈ finiteTypePoints X) :=
  sorry

/-- The closure of the finite-type points of an algebraic space inside a closed
subset `T` is `T`. -/
theorem closure_inter_finiteTypePoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    {T : Set (Points X)} (hT : IsClosed T) :
    closure (T ∩ finiteTypePoints X) = T :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
