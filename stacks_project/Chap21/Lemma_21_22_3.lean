module

public import ReasLib.RingTheory.Topology.Adic.InverseLimit
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.22.3

The Noetherian associated-graded argument is a general theorem about sequential inverse systems.
The reusable owner takes the ideal-compatible filtration and a surjective linear map from a
Noetherian graded source directly, so no chapter-local quotient presentation is required.
-/

/- Lemma 21.22.3 (0GYS): a surjective map from a Noetherian module onto the associated graded of
an ideal-compatible inverse-limit filtration identifies the limit topology with the adic
topology. -/
@[stacks 0GYS]
#check @CategoryTheory.SequentialInverseSystem.limitTopology_eq_adic_of_surjective

#check @CategoryTheory.SequentialInverseSystem.IsIdealCompatible
#check @CategoryTheory.SequentialInverseSystem.idealFiltration
#check @CategoryTheory.SequentialInverseSystem.limitTopology_eq_adic_of_isNoetherian
