/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.JacobsonSpace
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap68.Lemma_68_23_1_Jacobson

/-!
# Jacobson algebraic spaces and Jacobson spaces of points

For a decent algebraic space, the étale-local Jacobson property is equivalent to
the topological Jacobson property of the space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.23.4: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Then `X` is Jacobson if and only if `Points X` is Jacobson. -/
@[stacks 0BA6]
theorem isJacobson_iff_jacobsonSpace {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] :
    IsJacobson X ↔ JacobsonSpace (Points X) :=
  sorry

/-- A decent Jacobson algebraic space has Jacobson space of points. -/
theorem jacobsonSpace_of_isJacobson {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] [IsJacobson X] :
    JacobsonSpace (Points X) :=
  sorry

/-- A decent algebraic space whose space of points is Jacobson is Jacobson. -/
theorem isJacobson_of_jacobsonSpace {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (h : JacobsonSpace (Points X)) :
    IsJacobson X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
