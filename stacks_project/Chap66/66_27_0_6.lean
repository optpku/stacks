/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.«66_27_0_6_Site»
public import stacks_project.Chap66.«66_27_0_6_Comparison»
import StacksCheckRecall

@[expose] public section

/- 66.27.0.6: if `f : X ⟶ Y` is étale between algebraic spaces and `X` is an affine scheme, then
`X` is an object of `Y_affine,étale` and the affine étale ringed sites are identified
`(X_affine,étale, 𝒪_X) = (Y_affine,étale / X, 𝒪_Y |_{Y_affine,étale / X})` as
`affineEtaleLocalizationIso`. -/
@[stacks 04M3] #check AlgebraicGeometry.AlgebraicSpace.affineEtaleLocalizationIso
