module

public import ReasLib.Topology.IrreducibleComponents.Connected
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.8.17

The connected-union deletion theorem is owned by
`ReasLib.Topology.IrreducibleComponents.Connected`.
-/

/- Lemma 5.8.17: one component can be omitted while preserving connectedness. -/
@[stacks 0GM3]
#check @exists_connected_union_irreducibleComponents_except
