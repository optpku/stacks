/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.«66_27_0_4_Comparison»
import StacksCheckRecall

@[expose] public section

/- 66.27.0.4: if `f : X ⟶ Y` is étale between algebraic spaces and `X` is a scheme, then
`X` is an object of `Y_étale` and the small étale ringed sites are identified
`(X_étale, 𝒪_X) = (Y_étale / X, 𝒪_Y |_{Y_étale / X})` as `etaleLocalizationIso`. -/
@[stacks 04M1] #check AlgebraicGeometry.AlgebraicSpace.etaleLocalizationIso
