/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_21_14_Variant_for_Noetherian_Composition
public import stacks_project.Chap88.Definition_88_18_1_Ring

/-!
# Rig-smoothness is stable under composition for Noetherian adic rings
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

namespace TopologicalRing.Noetherian

/-- Lemma 88.17.5: The property `P φ` = "`φ` is rig-smooth" on arrows of
`WAdm^Noeth` is stable under composition as defined in Formal Spaces,
Remark 87.21.14. -/
@[stacks 0GCM]
theorem isStableUnderComposition_rigSmooth :
    IsStableUnderComposition
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigSmooth :=
  sorry

end TopologicalRing.Noetherian

namespace RingHom.RigSmooth

variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]
variable [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdicRing B] [IsNoetherianRing B]
variable [CommRing C] [TopologicalSpace C] [TopologicalRing.IsAdicRing C] [IsNoetherianRing C]

/-- The composite of rig-smooth homomorphisms of adic Noetherian topological rings
is rig-smooth. -/
instance comp {φ : A →+* B} {ψ : B →+* C} [RigSmooth φ] [RigSmooth ψ] :
    RigSmooth (ψ.comp φ) :=
  sorry

end RingHom.RigSmooth
