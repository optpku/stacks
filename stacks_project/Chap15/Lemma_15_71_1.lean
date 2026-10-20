module

public import ReasLib.LinearAlgebra.LinearMap.Factorisation.Projective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.71.1: maps factoring through projective modules

The reusable API is owned by `LinearMap.FactorsThroughProjective` and the submodule
`LinearMap.projectiveFactors`.

@stack 0G90
-/

/- Lemma 15.71.1 (1): a linear map factors through a projective module iff it factors through a
free module. -/
@[stacks 0G90 "(1), projective versus free factorisation"]
#check @LinearMap.FactorsThroughProjective.iff_free

/- Lemma 15.71.1 (2): maps factoring through projective modules form a submodule of the linear
hom module. -/
@[stacks 0G90 "(2), projective-factor submodule"]
#check @LinearMap.projectiveFactors

/- Lemma 15.71.1 (3): projective factorisation is preserved by arbitrary pre- and
postcomposition. -/
@[stacks 0G90 "(3), composition stability"]
#check @LinearMap.FactorsThroughProjective.comp

/- The structured midpoint API retains its module and projectivity instances. -/
#check @LinearMap.Factorisation.Projective
