module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.22.1: a separated morphism satisfies the uniqueness part of
the valuative criterion. -/
@[stacks 01KZ] #check IsSeparated.valuativeCriterion
