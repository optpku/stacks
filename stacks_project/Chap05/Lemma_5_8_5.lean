module

public import ReasLib.Topology.IrreducibleComponents.FiniteCover
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.8.5

The reusable finite-component cardinality comparison is owned by
`ReasLib.Topology.IrreducibleComponents.FiniteCover`.
-/

/- Lemma 5.8.5: continuous surjections do not increase a finite component count. -/
@[stacks 0GM2]
#check @irreducibleComponents_encard_le_of_surjective_continuous_of_encard_eq
