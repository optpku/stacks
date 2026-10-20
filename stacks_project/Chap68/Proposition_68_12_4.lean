/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Sober
import StacksCheckRecall

/-!
# Decent algebraic spaces have sober points

The space of points of a decent algebraic space is sober in the sense of
Topology, Definition 5.8.6, i.e. both Kolmogorov and quasi-sober.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Proposition 68.12.4: Let `S` be a scheme. Let `X` be a decent algebraic space
over `S`. Then the topological space `Points X` is sober in the sense of Topology,
Definition 5.8.6, i.e. a `T0Space` and `QuasiSober`. -/
@[stacks 03K6] #check (AlgebraicGeometry.AlgebraicSpace.points_sober_of_isDecent :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X],
    T0Space (Points X) ∧ QuasiSober (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.instQuasiSoberPoints :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X], QuasiSober (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.existsUnique_isGenericPoint_of_isDecent :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] {T : Set (Points X)},
    IsIrreducible T → IsClosed T → ∃! x : Points X, IsGenericPoint x T)

end AlgebraicGeometry.AlgebraicSpace
