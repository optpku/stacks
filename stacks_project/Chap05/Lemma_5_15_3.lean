module

public import Mathlib.Topology.Constructible
import StacksCheckRecall

@[expose] public section

/- Lemma 5.15.3: if `f : X → Y` is continuous and inverse images of retrocompact open subsets are
retrocompact, then inverse images of constructible subsets are constructible. -/
@[stacks 005I "constructible preimages under maps preserving retrocompact opens"]
#check Topology.IsConstructible.preimage
