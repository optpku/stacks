module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.23.3: a monomorphism of schemes is separated. -/
@[stacks 01L4] #check IsSeparated.isSeparated_of_mono
