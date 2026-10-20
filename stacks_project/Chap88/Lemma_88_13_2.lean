module

public import ReasLib.RingTheory.Topology.Flat.BaseChange
import StacksCheckRecall

/-!
# Flatness is stable under completed base change for Noetherian adic rings
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

namespace TopologicalRing.Noetherian

/- Lemma 88.13.2 (1): The property `P φ` = "`φ` is flat" on arrows of
`WAdm^Noeth` is stable under completed base change by the property of
Lemma 88.12.1, viewed as a property of arrows of `WAdm^Noeth`, in the
sense of Formal Spaces, Remark 87.21.10. -/
@[stacks 0GCA]
#check (TopologicalRing.Noetherian.isStableUnderBaseChangeBy_flat_isFiniteTypeOnReduction :
    IsLocalMorphismProperty.IsStableUnderBaseChangeBy
      (fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.Flat)
      (fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.IsFiniteTypeOnReduction))

/- Lemma 88.13.2 (2): The property `P + R` on arrows of `WAdm^Noeth`,
where `R φ` means that `φ` is adic and topologically of finite type as in
Lemma 88.11.1, is stable under completed base change in the sense of
Formal Spaces, Remark 87.21.9. -/
@[stacks 0GCA]
#check (TopologicalRing.Noetherian.isStableUnderBaseChange_flat_and_isAdicHom_and_topologicallyOfFiniteType :
    IsLocalMorphismProperty.IsStableUnderBaseChange
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.Flat ∧ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType)

end TopologicalRing.Noetherian
