/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_21_5_Variant_for_Noetherian_MorphismProperty
public import stacks_project.Chap88.Definition_88_18_1_Ring

/-!
# Rig-smoothness is a local morphism property of Noetherian adic rings
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

namespace TopologicalRing.Noetherian

/-- Lemma 88.17.3: The property `P φ` = "`φ` is rig-smooth" on arrows of
`WAdm^Noeth` is a local property as defined in Formal Spaces, Remark 87.21.5. -/
@[stacks 0GCK]
theorem isLocalMorphismProperty_rigSmooth :
    IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigSmooth :=
  sorry

end TopologicalRing.Noetherian
