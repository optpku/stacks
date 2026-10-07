module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_21_5_Variant_for_Noetherian_MorphismProperty
public import stacks_project.Chap88.Definition_88_20_1_Ring

/-!
# Rig-étaleness is a local morphism property of Noetherian adic rings
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

namespace TopologicalRing.Noetherian

/-- Lemma 88.19.3: The property `P φ` = "`φ` is rig-étale" on arrows of
`WAdm^Noeth` is a local property as defined in Formal Spaces, Remark 87.21.5. -/
@[stacks 0AQL]
theorem isLocalMorphismProperty_rigEtale :
    IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigEtale :=
  sorry

end TopologicalRing.Noetherian
