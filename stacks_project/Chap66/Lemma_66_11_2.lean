module

public import stacks_project.Chap66.Lemma_66_11_1
public import stacks_project.Chap66.Lemma_66_4_6_Topology

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.11.2: the codimension-zero points of an algebraic space are dense
in its canonical topological space of points. -/
@[stacks 0BAR]
theorem dense_setOf_localRingDimAt_eq_zero {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Dense (setOf fun x : Points X ↦ localRingDimAt x = 0) := sorry

end AlgebraicGeometry.AlgebraicSpace
