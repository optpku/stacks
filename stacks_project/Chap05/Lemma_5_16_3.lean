module

public import ReasLib.Topology.Constructible.Irreducible
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.16.3

Constructible irreducible-trace criteria are owned by
`ReasLib.Topology.Constructible.Irreducible`.
-/

/- Lemma 5.16.3: constructible traces satisfy the open-or-not-dense dichotomy. -/
@[stacks 053Z]
#check @Topology.IsConstructible.exists_nonemptyOpen_subset_trace_or_not_dense

/- Lemma 5.16.3: the dichotomy characterizes constructible subsets in Noetherian spaces. -/
@[stacks 053Z]
#check @Topology.IsConstructible.iff_forall_irreducibleClosed
