/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_22_1_Comparison
import StacksCheckRecall

open AlgebraicGeometry AlgebraicSpace GeometricPoint
open GeometricPoint.SmallEtaleNeighborhood

universe u

@[expose] public section

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {xbar : GeometricPoint X}
variable (N : SmallEtaleNeighborhood xbar)

/- Lemma 66.22.1 (1): the étale-site stalk `𝒪_{X, xbar}` of the structure sheaf of `X`
identifies with the étale-site stalk `𝒪_{U, ubar}` of a scheme étale neighbourhood
`(U, ubar)` of `xbar`. -/
@[stacks 04KF] #check AlgebraicSpace.etaleLocalRing_etaleNeighborhood

/- Lemma 66.22.1 (2): the étale-site stalk `𝒪_{U, ubar}` is a strict henselization of the
Zariski local ring of `U` at the center `u` of `ubar`. -/
@[stacks 04KF] #check
  Scheme.etaleLocalRing.instIsStrictHenselizationOf N.scheme (schemeGeometricPoint N)
