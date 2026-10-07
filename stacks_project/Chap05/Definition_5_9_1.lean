module

public import ReasLib.Topology.Noetherian.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 5.9.1

The reusable local Noetherian API is owned by `ReasLib.Topology.Noetherian`.
-/

/- Definition 5.9.1 (1): the canonical global Noetherian-space predicate. -/
@[stacks 0051 "Noetherian topological spaces"]
#check @TopologicalSpace.NoetherianSpace

/- Definition 5.9.1 (2): the canonical locally Noetherian-space predicate. -/
@[stacks 0051 "locally Noetherian topological spaces"]
#check @TopologicalSpace.LocallyNoetherianSpace
