module

public import stacks_project.Chap61.«61_5_2_6_Diagram»
public import stacks_project.Chap61.«61_5_2_6_Scheme»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.WLocal.Construction

/- 61.5.2.6 (1): the affine scheme `X_w` is a limit of the inverse system
`X_E` of finite-stage spectra, as `E` runs over the directed poset of finite
subsets of `A`. -/
@[stacks 0974] #check isLimit_schemeCone

/- 61.5.2.6 (2): the closed subscheme `Z` is a limit of the inverse system
`Z_E` of finite-stage closed subschemes. -/
@[stacks 0974] #check isLimit_closedCone

/- 61.5.2.6 (3): the inclusion `Z ⟶ X_w` is a closed immersion, so
`X_w ⊃ Z` as a closed subscheme. -/
@[stacks 0974] #check isClosedImmersion_closedι

#check scheme
#check closedSubscheme
#check closedι
#check ring
