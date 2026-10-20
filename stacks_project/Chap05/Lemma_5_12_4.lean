module

public import Mathlib.Topology.Separation.Hausdorff
import StacksCheckRecall

@[expose] public section

/- Lemma 5.12.4 (1): in a Hausdorff space, every quasi-compact subset is closed. Mathlib's
`IsCompact` is the source's quasi-compactness condition for subsets. -/
@[stacks 08YB "quasi-compact subsets of Hausdorff spaces are closed"]
#check IsCompact.isClosed

/- The canonical predicate `SeparatedNhds E₁ E₂` unfolds to exactly the source's open supersets
with empty intersection. Thus `SeparatedNhds.of_isCompact_isCompact` preserves the Hausdorff,
compactness, and disjointness boundary while exposing the reusable neighborhood-separation API. -/

/- Lemma 5.12.4 (2): disjoint quasi-compact subsets of a Hausdorff space admit disjoint open
neighborhoods. -/
@[stacks 08YB "disjoint quasi-compact subsets have disjoint open neighborhoods"]
#check SeparatedNhds.of_isCompact_isCompact
