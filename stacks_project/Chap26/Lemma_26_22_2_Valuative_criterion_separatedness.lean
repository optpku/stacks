module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.22.2 (Valuative criterion separatedness): a quasi-separated
morphism satisfying uniqueness in the valuative criterion is separated. -/
@[stacks 01L0] #check IsSeparated.of_valuativeCriterion
