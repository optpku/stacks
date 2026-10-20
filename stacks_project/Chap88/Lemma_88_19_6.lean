module

public import ReasLib.RingTheory.AdicCompletion.RigEtale.Cancellation
import StacksCheckRecall

/-!
# Cancellation for rig-étale morphisms of Noetherian adic rings
-/

@[expose] public section

universe u

open TopologicalRing TopologicalRing.Noetherian RingHom

/- Lemma 88.19.6: The property `P φ` = "`φ` is rig-étale" on arrows of
`WAdm^Noeth` has the cancellation property as defined in Formal Spaces,
Remark 87.21.18. -/
@[stacks 0GCY] #check (TopologicalRing.Noetherian.hasCancellationProperty_rigEtale :
    HasCancellationProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigEtale)
