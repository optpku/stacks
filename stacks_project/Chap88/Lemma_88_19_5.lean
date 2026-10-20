module

public import ReasLib.RingTheory.AdicCompletion.RigEtale.Composition
import StacksCheckRecall

/-!
# Rig-étaleness is stable under composition for Noetherian adic rings
-/

@[expose] public section

universe u

/- Lemma 88.19.5: The property `P φ` = "`φ` is rig-étale" on arrows of
`WAdm^Noeth` is stable under composition as defined in Formal Spaces,
Remark 87.21.14. -/
@[stacks 0GCX] #check (TopologicalRing.Noetherian.isStableUnderComposition_rigEtale :
    TopologicalRing.Noetherian.IsStableUnderComposition
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigEtale)
