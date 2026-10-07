module

public import stacks_project.Chap87.Definition_87_34_1_Site
import StacksCheckRecall

@[expose] public section

/- Definition 87.34.1 (1): let `S` be a scheme and let `X` be a formal algebraic
space over `S` with reduction `reduction X`. The small étale site `X_étale` of
`X` is the small étale site of `reduction X`, recorded as
`smallEtaleTopology X`. -/
@[stacks 0DEA] #check AlgebraicGeometry.FormalAlgebraicSpace.smallEtaleTopology

/- Definition 87.34.1 (2): the site `X_spaces,étale` of a formal algebraic space
`X` is the étale site of algebraic spaces over `reduction X`, recorded as
`spacesEtaleTopology X`. -/
@[stacks 0DEA] #check AlgebraicGeometry.FormalAlgebraicSpace.spacesEtaleTopology

/- Definition 87.34.1 (3): the site `X_affine,étale` of a formal algebraic space
`X` is the affine étale site of `reduction X`, recorded as
`affineEtaleTopology X`. -/
@[stacks 0DEA] #check AlgebraicGeometry.FormalAlgebraicSpace.affineEtaleTopology
