module

public import ReasLib.RingTheory.AdicCompletion.RigFlat.Composition
import StacksCheckRecall

/-!
# Rig-flatness is stable under composition for Noetherian adic rings
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

/- Lemma 88.15.10: The property `P φ` = "`φ` is rig-flat" on arrows of
`WAdm^Noeth` is stable under composition as defined in Formal Spaces,
Remark 87.21.14. -/
@[stacks 0GGV]
#check (TopologicalRing.Noetherian.isStableUnderComposition_rigFlat :
    IsStableUnderComposition
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigFlat)

variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]
variable [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdicRing B] [IsNoetherianRing B]
variable [CommRing C] [TopologicalSpace C] [TopologicalRing.IsAdicRing C] [IsNoetherianRing C]

#check (RingHom.RigFlat.comp :
    ∀ {φ : A →+* B} {ψ : B →+* C} [φ.RigFlat] [ψ.RigFlat],
      (ψ.comp φ).RigFlat)
