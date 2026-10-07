module

public import Mathlib.Topology.Compactness.Compact
import StacksCheckRecall

@[expose] public section

/- `IsCompact.inter_iInter_nonempty` is the set-level theorem, while
`CompactSpace.iInter_nonempty` specializes it to the whole space with exactly the source
hypotheses. Recalling the specialization keeps quasi-compactness at the separation-free
`CompactSpace` owner and avoids a parallel local wrapper. -/

/- Lemma 5.12.6: in a quasi-compact topological space, a family of closed subsets with the finite
intersection property has nonempty total intersection. Via Definition 5.12.1, quasi-compact spaces
are `CompactSpace`, and this is exactly the canonical theorem `CompactSpace.iInter_nonempty`. -/
@[stacks 005D "finite intersection property for closed subsets of a quasi-compact space"]
#check CompactSpace.iInter_nonempty
