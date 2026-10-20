module

public import Mathlib.Topology.Irreducible
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.8.2

The source is the global-continuity specialization of Mathlib's stronger
`ContinuousOn` image theorem.
-/

/- Lemma 5.8.2: continuous images of irreducible subsets are irreducible. -/
@[stacks 0379 "continuous images of irreducible subsets"]
#check @IsIrreducible.image
