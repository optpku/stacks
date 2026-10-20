module

public import ReasLib.RingTheory.AdicCompletion.RigSmooth.Composition
import StacksCheckRecall

/-!
# Rig-smoothness is stable under composition for Noetherian adic rings
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

/- Lemma 88.17.5: The property `P φ` = "`φ` is rig-smooth" on arrows of
`WAdm^Noeth` is stable under composition as defined in Formal Spaces,
Remark 87.21.14. -/
@[stacks 0GCM] #check (TopologicalRing.Noetherian.isStableUnderComposition_rigSmooth :
    TopologicalRing.Noetherian.IsStableUnderComposition
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigSmooth)

#check (RingHom.RigSmooth.comp :
    ∀ {A B C : Type u}
      [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdicRing B] [IsNoetherianRing B]
      [CommRing C] [TopologicalSpace C] [TopologicalRing.IsAdicRing C] [IsNoetherianRing C]
      {φ : A →+* B} {ψ : B →+* C} [RingHom.RigSmooth φ] [RingHom.RigSmooth ψ],
      RingHom.RigSmooth (ψ.comp φ))
