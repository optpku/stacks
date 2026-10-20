module

public import ReasLib.RingTheory.Topology.WeaklyAdmissible.Composition
import StacksCheckRecall

@[expose] public section

universe u

open TopologicalRing

/- Situation 87.21.11: the source considers a local property P of morphisms of
WAdm^count in the sense of Situation 87.21.2. The stability condition itself is
defined independently of locality: for continuous φ : B →+* A and ψ : C →+* B,
P φ and P ψ imply P (φ.comp ψ). -/
@[stacks 0GBH] #check (TopologicalRing.IsStableUnderComposition :
    (∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop) → Prop)
