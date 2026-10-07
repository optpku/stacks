module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.RingHom.Flat
public import stacks_project.Chap87.Remark_87_21_14_Variant_for_Noetherian_Composition

/-!
# Flatness is stable under composition for Noetherian adic rings
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

namespace TopologicalRing.Noetherian

/-- Lemma 88.13.3: The property `P φ` = "`φ` is flat" on arrows of
`WAdm^Noeth` is stable under composition as defined in Formal Spaces,
Remark 87.21.14. -/
@[stacks 0GCB]
theorem isStableUnderComposition_flat :
    IsStableUnderComposition
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.Flat :=
  sorry

end TopologicalRing.Noetherian
