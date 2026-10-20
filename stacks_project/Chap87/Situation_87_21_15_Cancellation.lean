module

public import ReasLib.RingTheory.Topology.WeaklyAdmissible.Cancellation

@[expose] public section

universe u

open TopologicalRing

/- Cancellation for properties of continuous morphisms of countably indexed
weakly admissible rings. -/
#check (TopologicalRing.HasCancellationProperty :
  (∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop) → Prop)
