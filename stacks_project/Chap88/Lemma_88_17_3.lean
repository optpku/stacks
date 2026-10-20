module

public import ReasLib.RingTheory.AdicCompletion.RigSmooth.Locality
import StacksCheckRecall

/-!
# Rig-smoothness is a local morphism property of Noetherian adic rings
-/

@[expose] public section

universe u

/- Lemma 88.17.3: The property `P φ` = "`φ` is rig-smooth" on arrows of
`WAdm^Noeth` is a local property as defined in Formal Spaces, Remark 87.21.5. -/
@[stacks 0GCK] #check (TopologicalRing.Noetherian.isLocalMorphismProperty_rigSmooth :
    TopologicalRing.Noetherian.IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigSmooth)
