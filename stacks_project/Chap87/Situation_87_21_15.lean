module

public import ReasLib.RingTheory.Topology.WeaklyAdmissible.Cancellation
import StacksCheckRecall

@[expose] public section

universe u

open TopologicalRing

/- Situation 87.21.15: a local property P of morphisms of WAdm^count (see
Situation 87.21.2) has the cancellation property when, for morphisms B → A
and C → B, P(C → B) and P(C → A) imply P(B → A). -/
@[stacks 0GBL] #check (TopologicalRing.HasCancellationProperty :
  (∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop) → Prop)
