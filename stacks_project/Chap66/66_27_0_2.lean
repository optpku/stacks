module

public import stacks_project.Chap66.«66_27_0_2_Comparison»
public import stacks_project.Chap66.«66_27_0_2_RingedSite»
import StacksCheckRecall

@[expose] public section

/- 66.27.0.2: if `f : X ⟶ Y` is étale between algebraic spaces, then `X` is an object of
`Y_spaces,étale` and the ringed sites are identified
`(X_spaces,étale, 𝒪_X) = (Y_spaces,étale / X, 𝒪_Y |_{Y_spaces,étale / X})` as
`spacesEtaleLocalizationIso`. -/
@[stacks 04LZ] #check AlgebraicGeometry.AlgebraicSpace.spacesEtaleLocalizationIso
