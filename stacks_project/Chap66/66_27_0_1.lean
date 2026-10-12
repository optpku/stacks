/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.«66_27_0_1_Comparison»
import StacksCheckRecall

@[expose] public section

/- 66.27.0.1: if `f : X ⟶ Y` is étale between algebraic spaces, then `X` is an object of
`Y_spaces,étale` and the sites are identified `X_spaces,étale = Y_spaces,étale / X` as
`spacesEtaleLocalizationEquivalence`. -/
@[stacks 04LY] #check AlgebraicGeometry.AlgebraicSpace.spacesEtaleLocalizationEquivalence
