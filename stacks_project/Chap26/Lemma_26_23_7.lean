module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.23.7: injectivity on points together with surjectivity on all
stalk maps implies monomorphism. -/
@[stacks 01L6]
#check SurjectiveOnStalks.mono_of_injective
