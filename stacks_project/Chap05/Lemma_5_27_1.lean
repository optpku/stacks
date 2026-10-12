/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.CompactOpen.Refinement
import StacksCheckRecall

@[expose] public section

universe u

open Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X]

/- Lemma 5.27.1 (1): a compact-open basis supplies local quasi-compactness. -/
@[stacks 0069 "compact-open bases imply local quasi-compactness"]
#check (fun [PrespectralSpace X] [QuasiSeparatedSpace X] ↦
  (inferInstance : LocallyCompactSpace X))

/- Lemma 5.27.1 (2): compact opens are retrocompact in a quasi-separated space. -/
@[stacks 0069 "quasi-compact opens are retrocompact"]
#check (fun [PrespectralSpace X] [QuasiSeparatedSpace X] (U : CompactOpens X) ↦
  U.isCompact.isRetrocompact U.isOpen)

/- Lemma 5.27.1 (3): the reusable finite compact-open refinement includes compact overlaps. -/
@[stacks 0069 "finite subordinate compact-open coverings with compact overlaps"]
#check CompactOpens.FiniteCoverRefinement.exists_withCompactIntersections
#check CompactOpens.FiniteCoverRefinement.nonempty_of_cover

/- A refinement witness exposes its finite family, cover equation, subordination data, and the
optional compact-intersection property without repeated conjunction elimination. -/
#check CompactOpens.FiniteCoverRefinement
#check CompactOpens.FiniteCoverRefinement.ofFinset
#check CompactOpens.FiniteCoverRefinement.HasCompactIntersections
