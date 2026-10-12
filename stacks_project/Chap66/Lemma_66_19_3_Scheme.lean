/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_19_2_EtaleNeighborhood
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme

open CategoryTheory AlgebraicGeometry

universe u

@[expose] public section

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood

/-- Every étale neighborhood of a geometric point of an algebraic space is refined by one whose
underlying algebraic space is a scheme. -/
theorem exists_isScheme {S : Scheme.{u}} {X : AlgebraicSpace S} {xbar : GeometricPoint X}
    (U : EtaleNeighborhood xbar) :
    ∃ (U' : EtaleNeighborhood xbar) (_ : U' ⟶ U), IsScheme U'.space := sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood
