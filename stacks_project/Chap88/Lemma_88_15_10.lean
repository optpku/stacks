module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_21_14_Variant_for_Noetherian_Composition
public import stacks_project.Chap88.Lemma_88_15_8_RigFlat

/-!
# Rig-flatness is stable under composition for Noetherian adic rings
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

namespace TopologicalRing.Noetherian

/-- Lemma 88.15.10: The property `P φ` = "`φ` is rig-flat" on arrows of
`WAdm^Noeth` is stable under composition as defined in Formal Spaces,
Remark 87.21.14. -/
@[stacks 0GGV]
theorem isStableUnderComposition_rigFlat :
    IsStableUnderComposition
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigFlat :=
  sorry

end TopologicalRing.Noetherian

namespace RingHom.RigFlat

variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]
variable [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdicRing B] [IsNoetherianRing B]
variable [CommRing C] [TopologicalSpace C] [TopologicalRing.IsAdicRing C] [IsNoetherianRing C]

/-- The composite of rig-flat homomorphisms of adic Noetherian topological rings
is rig-flat. -/
instance comp {φ : A →+* B} {ψ : B →+* C} [RigFlat φ] [RigFlat ψ] :
    RigFlat (ψ.comp φ) :=
  sorry

end RingHom.RigFlat
