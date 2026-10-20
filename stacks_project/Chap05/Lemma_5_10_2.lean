module

public import ReasLib.Topology.KrullDimension.Local
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.10.2

The global-to-local Krull-dimension equality is owned by
`ReasLib.Topology.KrullDimension.Local`.
-/

/- Lemma 5.10.2: global topological Krull dimension is the supremum of the local dimensions. -/
@[stacks 0B7I]
#check @topologicalKrullDim_eq_iSup_topologicalKrullDimAt
