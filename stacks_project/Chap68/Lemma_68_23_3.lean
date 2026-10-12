/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.JacobsonSpace
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Lemma_67_25_4_FiniteTypePoint
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap68.Lemma_68_23_1_Jacobson

/-!
# Finite-type points of decent Jacobson algebraic spaces

On a decent Jacobson algebraic space, the finite-type points are exactly the
closed points of the space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.23.3: Let `S` be a scheme. Let `X` be a decent Jacobson algebraic space
over `S`. Then `finiteTypePoints X` is the set of closed points of `Points X`. -/
@[stacks 0BA5]
theorem finiteTypePoints_eq_closedPoints {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [IsJacobson X] :
    finiteTypePoints X = closedPoints (Points X) :=
  sorry

/-- A point of a decent Jacobson algebraic space is a finite-type point if and only
if it is a closed point of `Points X`. -/
theorem mem_finiteTypePoints_iff_mem_closedPoints {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] [IsJacobson X] {x : Points X} :
    x ∈ finiteTypePoints X ↔ x ∈ closedPoints (Points X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
