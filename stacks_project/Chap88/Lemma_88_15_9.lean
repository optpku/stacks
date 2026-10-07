module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_21_5_Variant_for_Noetherian_MorphismProperty
public import stacks_project.Chap88.Lemma_88_15_8_RigFlat

/-!
# Rig-flatness is a local morphism property of Noetherian adic rings
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

namespace TopologicalRing.Noetherian

/-- Lemma 88.15.9: The property `P φ` = "`φ` is rig-flat" on arrows of
`WAdm^Noeth` is a local property as defined in Formal Spaces, Remark 87.21.4,
recorded as `IsLocalMorphismProperty` of `fun φ ↦ φ.RigFlat`. -/
@[stacks 0GGU]
theorem isLocalMorphismProperty_rigFlat :
    IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigFlat :=
  sorry

end TopologicalRing.Noetherian
