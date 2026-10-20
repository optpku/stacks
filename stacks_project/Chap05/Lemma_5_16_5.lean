module

public import ReasLib.Topology.Constructible.Neighborhood
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.16.5

The irreducible-closed openness criterion is owned by
`ReasLib.Topology.Constructible.Neighborhood`.
-/

/- Lemma 5.16.5: open subsets are characterized by their irreducible closed traces. -/
@[stacks 0541]
#check @Topology.isOpen_iff_forall_irreducibleCloseds_inter_empty_or_contains_nonempty_open
