module

public import ReasLib.RingTheory.AdicCompletion.RigFlat.CompletedBaseChange
import StacksCheckRecall

/-!
# Rig-flatness is stable under completed base change
-/

@[expose] public section

universe u

/- Lemma 88.15.6: rig-flatness is stable under adic, topologically finite-type
completed base change of adic Noetherian rings. -/
@[stacks 0GGR] #check (RingHom.RigFlat.completedBaseChange :
    ∀ {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [TopologicalRing.IsAdicRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [RingHom.RigFlat (algebraMap A B)]
    [h_adic : Fact ((algebraMap A C).IsAdicHom)]
    [h_tft : Fact ((algebraMap A C).TopologicallyFiniteType)],
      RingHom.RigFlat (Algebra.TensorProduct.Completed.includeRight A B C))
