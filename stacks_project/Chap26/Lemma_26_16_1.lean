module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Limits

@[expose] public section

open AlgebraicGeometry CategoryTheory.Limits

/- Lemma 26.16.1: schemes have finite limits, hence a final object,
products, and fibre products. -/
@[stacks 01JM] #check (inferInstance : HasFiniteLimits Scheme)
