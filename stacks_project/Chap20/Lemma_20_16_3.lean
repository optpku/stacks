/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.Cohomology.CompactSubset
import StacksCheckRecall

@[expose] public section

/- Lemma 20.16.3 (09V3): for a quasi-compact subset whose points have pairwise disjoint ambient
open neighbourhoods, the canonical map from the colimit of cohomology over open neighbourhoods
to the cohomology of the restricted sheaf is an isomorphism.  Compactness is bundled by
`Compacts`, and the ambient separation hypothesis is Mathlib's `Set.PairwiseDisjoint 𝓝`. -/
@[stacks 09V3]
#check @TopCat.Sheaf.Cohomology.CompactSubset.comparison_isIso

#check @TopCat.Sheaf.Cohomology.CompactSubset.diagram
#check @TopCat.Sheaf.Cohomology.CompactSubset.stageMap
#check @TopCat.Sheaf.Cohomology.CompactSubset.comparison
#check @TopCat.Sheaf.Cohomology.CompactSubset.ι_comp_comparison
