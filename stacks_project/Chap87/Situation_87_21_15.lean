module

public import stacks_project.Chap87.Situation_87_21_15_Cancellation
import StacksCheckRecall

@[expose] public section

open TopologicalRing

/- Situation 87.21.15: a local property P of morphisms of WAdm^count (see
Situation 87.21.2) has the cancellation property when, for morphisms B → A
and C → B, P(C → B) and P(C → A) imply P(B → A). -/
@[stacks 0GBL] #check TopologicalRing.HasCancellationProperty
