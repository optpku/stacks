/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Separation.Basic
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Decent algebraic spaces have Kolmogorov points

The space of points of a decent algebraic space is a Kolmogorov space, i.e. a
`T0Space`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.12.3: Let `S` be a scheme. Let `X` be a decent algebraic space over
`S`. Then `Points X` is Kolmogorov in the sense of Topology, Definition 5.8.6,
i.e. a `T0Space`. -/
@[stacks 03K3]
instance instT0SpacePoints {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] :
    T0Space (Points X) :=
  sorry

/-- Mutual specialization of points of a decent algebraic space implies equality. -/
theorem eq_of_specializes_specializes {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {x x' : Points X} (h : Specializes x x') (h' : Specializes x' x) :
    x = x' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
