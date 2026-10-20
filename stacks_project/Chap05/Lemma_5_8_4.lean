module

public import ReasLib.Topology.IrreducibleComponents.FiniteCover
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.8.4

The finite irredundant-cover recognition theorem is owned by
`ReasLib.Topology.IrreducibleComponents.FiniteCover`.
-/

/- Lemma 5.8.4: an irredundant finite closed irreducible cover is the component set. -/
@[stacks 0G2Y]
#check @irreducibleComponents_eq_of_finite_irreducible_closed_cover
