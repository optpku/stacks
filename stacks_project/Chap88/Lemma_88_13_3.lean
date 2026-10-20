module

public import ReasLib.RingTheory.Topology.Noetherian.Flat
import StacksCheckRecall

/-!
# Flatness is stable under composition for Noetherian adic rings
-/

@[expose] public section

universe u

/- Lemma 88.13.3: The property `P φ` = "`φ` is flat" on arrows of
`WAdm^Noeth` is stable under composition as defined in Formal Spaces,
Remark 87.21.14. -/
@[stacks 0GCB] #check (TopologicalRing.Noetherian.isStableUnderComposition_flat :
    TopologicalRing.Noetherian.IsStableUnderComposition
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A]
        [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdicRing B]
        [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.Flat)
