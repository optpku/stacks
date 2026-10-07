module

public import stacks_project.Chap61.Lemma_61_14_1_Hypercovering
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

/- Lemma 61.14.1 (1): for every object `U` of the small pro-étale site `X.ProEt`
there exists a hypercovering `K` of `U` whose every degree family is a singleton
weakly contractible object covering `U`. -/
@[stacks 09A1] #check ProEt.exists_hypercovering_isWeaklyContractibleSingleton

/- Lemma 61.14.1 (2): for every quasi-compact and quasi-separated object `U` of
`X.ProEt` there exists a hypercovering `K` of `U` whose every degree family is a
singleton affine weakly contractible object covering `U`. -/
@[stacks 09A1] #check ProEt.exists_hypercovering_isAffine_isWeaklyContractibleSingleton
