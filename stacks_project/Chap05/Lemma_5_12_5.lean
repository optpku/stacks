module

public import ReasLib.Topology.Compactness.Closed
import StacksCheckRecall

@[expose] public section

/- Lemma 5.12.5: for a subset of a quasi-compact Hausdorff space, closedness is equivalent to
quasi-compactness. The separation-free and Hausdorff directions are Mathlib's
`IsClosed.isCompact` and `IsCompact.isClosed`; ReasLib exposes their compact-Hausdorff iff form. -/
@[stacks 08YC "closed subsets and quasi-compact subsets of compact Hausdorff spaces"]
#check @CompactSpace.isClosed_iff_isCompact
