/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.«66_27_0_5_Site»
public import stacks_project.Chap66.«66_27_0_5_Comparison»
import StacksCheckRecall

@[expose] public section

/- 66.27.0.5: if `f : ofOver U ⟶ Y` is étale of algebraic spaces and `U.left` is an affine
scheme, then `ofOver U` is an object of `Y_{affine,étale}` and the affine étale sites are
identified `X_{affine,étale} = Y_{affine,étale} / X` by `affineEtaleLocalizationEquiv`. -/
@[stacks 04M2] #check AlgebraicGeometry.AlgebraicSpace.affineEtaleLocalizationEquiv
