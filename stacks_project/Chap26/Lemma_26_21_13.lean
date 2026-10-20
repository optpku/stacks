module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.21.13 (1): separatedness descends from a composite to its first factor. -/
@[stacks 01KV] #check IsSeparated.of_comp

/- Lemma 26.21.13 (2): quasi-separatedness descends from a composite to its first factor. -/
@[stacks 01KV] #check QuasiSeparated.of_comp
