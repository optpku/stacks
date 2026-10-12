/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sober
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_4_6_Topology

/-!
# Sobriety of Zariski locally quasi-separated algebraic spaces

The space of points of a Zariski locally quasi-separated algebraic space is sober
in the sense of Topology, Definition 5.8.6, i.e. both Kolmogorov and quasi-sober.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.15.1: let `S` be a scheme. Let `X` be a Zariski locally quasi-separated
algebraic space over `S`. Then the topological space `Points X` is sober. -/
@[stacks 06NJ]
theorem points_sober {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelyZariskiLocallyQuasiSeparated X] :
    T0Space (Points X) ∧ QuasiSober (Points X) :=
  sorry

namespace IsAbsolutelyZariskiLocallyQuasiSeparated

/-- The space of points of a Zariski locally quasi-separated algebraic space is Kolmogorov. -/
instance instT0SpacePoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelyZariskiLocallyQuasiSeparated X] : T0Space (Points X) :=
  sorry

/-- The space of points of a Zariski locally quasi-separated algebraic space is quasi-sober. -/
instance instQuasiSoberPoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelyZariskiLocallyQuasiSeparated X] : QuasiSober (Points X) :=
  sorry

/-- Every irreducible closed subset of `Points X` has a unique generic point. -/
theorem existsUnique_isGenericPoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsAbsolutelyZariskiLocallyQuasiSeparated X] {T : Set (Points X)}
    (hT_irred : IsIrreducible T) (hT_closed : IsClosed T) :
    ∃! x : Points X, IsGenericPoint x T :=
  sorry

end IsAbsolutelyZariskiLocallyQuasiSeparated

end AlgebraicGeometry.AlgebraicSpace
