module

public import ReasLib.Topology.Catenary
import StacksCheckRecall

@[expose] public section

/-!
# Definition 5.11.4

The reusable catenary-space API is owned by `ReasLib.Topology.Catenary`.
-/

/- Definition 5.11.4: the canonical catenary-space predicate. -/
@[stacks 02I1]
#check @TopologicalSpace.CatenarySpace
