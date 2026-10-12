/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Constructible
import StacksCheckRecall

@[expose] public section

/-
Mathlib's `CompactSpace` is deliberately separation-free, so it matches the Stacks meaning of
quasi-compactness; `isCompact_iff_finite_subcover` gives the stated open-cover presentation.
Likewise, `IsSpectralMap` includes continuity and exactly the compact-preimage condition for
compact opens. For subsets, mathlib takes the intersection formulation `IsRetrocompact` as the
owner, while `IsRetrocompact_iff_isSpectralMap_subtypeVal` recovers the source's inclusion-map
formulation. These canonical owners avoid a parallel quasi-compactness wrapper and are directly
reusable by the later topology API.
-/

/- Definition 5.12.1 (1): a topological space is quasi-compact exactly in the canonical,
separation-free sense `CompactSpace`; equivalently, every open cover has a finite subcover. -/
@[stacks 005A "quasi-compact topological spaces"]
#check CompactSpace

/- Definition 5.12.1 (2): a continuous map is quasi-compact when inverse images of quasi-compact
open subsets are quasi-compact; this is the canonical predicate `IsSpectralMap`. -/
@[stacks 005A "quasi-compact maps"]
#check IsSpectralMap

/- Definition 5.12.1 (3): the canonical predicate for a retrocompact subset is
`IsRetrocompact`. -/
@[stacks 005A "retrocompact subsets"]
#check IsRetrocompact

/- Companion check: the source definition by quasi-compactness of the subset inclusion is exactly
the canonical subtype-inclusion characterization of `IsRetrocompact`. -/
#check IsRetrocompact_iff_isSpectralMap_subtypeVal
