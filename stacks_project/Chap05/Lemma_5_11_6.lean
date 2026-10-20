module

public import ReasLib.Topology.Catenary
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.11.6

The reusable finite-and-additive codimension characterization is owned by
`ReasLib.Topology.Catenary`.
-/

/- Lemma 5.11.6: catenarity is equivalent to finite, additive relative codimension. -/
@[stacks 02I6]
#check @TopologicalSpace.catenarySpace_iff_finite_codimBetween_and_codimBetween_additive
