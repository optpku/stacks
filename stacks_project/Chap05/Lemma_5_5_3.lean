module

public import ReasLib.Topology.Bases.Refinement
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.5.3

Refinement of an indexed open cover by a topological basis is owned by
`ReasLib.Topology.Bases.Refinement`.
-/

/- Lemma 5.5.3: an indexed open cover admits a refinement by basis members. -/
@[stacks 004Q]
#check @TopologicalSpace.IsTopologicalBasis.exists_refinement_of_openCover
