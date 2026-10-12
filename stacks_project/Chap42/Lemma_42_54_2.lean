/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap42.Lemma_42_54_2_BivariantClass

/- Lemma 42.54.2 (1): the deformation-to-the-normal-cone construction defines a completed
bivariant class `c(Z ⟶ X, 𝒩)`. -/
@[stacks 0FBK] #check @AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.closedClass

/- Lemma 42.54.2 (2): the completed class is compatible with cartesian base change as in
`Lemma 42.54.1`. -/
@[stacks 0FBK] #check @AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.closedClass_pullback

/- Lemma 42.54.2 (3): when `𝒩` has constant rank `r`, the completed class is represented by
its homogeneous degree-`r` bivariant class. -/
@[stacks 0FBK] #check
  @AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.closedClass_eq_completeOfRank
