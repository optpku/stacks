/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Dimension of decent algebraic spaces

On a decent algebraic space, étale-local dimension agrees with the topological
Krull dimension of the space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.12.5 (1): Let `S` be a scheme. Let `X` be a decent algebraic space over
`S`. If `x : Points X`, then `dimensionAt x = topologicalKrullDimAt x`. -/
@[stacks 0A4J]
theorem dimensionAt_eq_topologicalKrullDimAt_of_isDecent {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (x : Points X) :
    dimensionAt x = topologicalKrullDimAt x :=
  sorry

/-- Lemma 68.12.5 (2): Let `S` be a scheme. Let `X` be a decent algebraic space over
`S`. Then `dimension X = topologicalKrullDim (Points X)`. -/
@[stacks 0A4J]
theorem dimension_eq_topologicalKrullDim_of_isDecent {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] :
    dimension X = topologicalKrullDim (Points X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
