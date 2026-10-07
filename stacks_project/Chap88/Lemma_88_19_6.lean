module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_21_18_Variant_for_Noetherian_Cancellation
public import stacks_project.Chap88.Definition_88_20_1_Ring

/-!
# Cancellation for rig-étale morphisms of Noetherian adic rings
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

namespace TopologicalRing.Noetherian

/-- Lemma 88.19.6: The property `P φ` = "`φ` is rig-étale" on arrows of
`WAdm^Noeth` has the cancellation property as defined in Formal Spaces,
Remark 87.21.18. -/
@[stacks 0GCY]
theorem hasCancellationProperty_rigEtale :
    HasCancellationProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigEtale :=
  sorry

end TopologicalRing.Noetherian
