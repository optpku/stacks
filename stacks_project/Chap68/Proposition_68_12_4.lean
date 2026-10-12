/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sober
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Decent algebraic spaces have sober points

The space of points of a decent algebraic space is sober in the sense of
Topology, Definition 5.8.6, i.e. both Kolmogorov and quasi-sober.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Proposition 68.12.4: Let `S` be a scheme. Let `X` be a decent algebraic space
over `S`. Then the topological space `Points X` is sober in the sense of Topology,
Definition 5.8.6, i.e. a `T0Space` and `QuasiSober`. -/
@[stacks 03K6]
theorem points_sober_of_isDecent {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] :
    T0Space (Points X) ∧ QuasiSober (Points X) :=
  sorry

/-- The space of points of a decent algebraic space is quasi-sober. -/
instance instQuasiSoberPoints {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] :
    QuasiSober (Points X) :=
  sorry

/-- Every irreducible closed subset of `Points X` has a unique generic point. -/
theorem existsUnique_isGenericPoint_of_isDecent {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {T : Set (Points X)} (hT_irred : IsIrreducible T)
    (hT_closed : IsClosed T) :
    ∃! x : Points X, IsGenericPoint x T :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
