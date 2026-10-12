/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.RingHom.Flat
public import stacks_project.Chap87.Remark_87_21_9_Variant_for_Noetherian_BaseChange
public import stacks_project.Chap87.Remark_87_21_10_Another_variant_for_Noetherian_BaseChange
public import stacks_project.Chap88.Lemma_88_12_1_FiniteTypeReduction
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType

/-!
# Flatness is stable under completed base change for Noetherian adic rings
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

namespace TopologicalRing.Noetherian

/-- Lemma 88.13.2 (1): The property `P φ` = "`φ` is flat" on arrows of
`WAdm^Noeth` is stable under completed base change by the property of
Lemma 88.12.1, viewed as a property of arrows of `WAdm^Noeth`, in the
sense of Formal Spaces, Remark 87.21.10. -/
@[stacks 0GCA]
theorem isStableUnderBaseChangeBy_flat_isFiniteTypeOnReduction :
    IsLocalMorphismProperty.IsStableUnderBaseChangeBy
      (fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.Flat)
      (fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.IsFiniteTypeOnReduction) :=
  sorry

/-- Lemma 88.13.2 (2): The property `P + R` on arrows of `WAdm^Noeth`,
where `R φ` means that `φ` is adic and topologically of finite type as in
Lemma 88.11.1, is stable under completed base change in the sense of
Formal Spaces, Remark 87.21.9. -/
@[stacks 0GCA]
theorem isStableUnderBaseChange_flat_and_isAdicHom_and_topologicallyOfFiniteType :
    IsLocalMorphismProperty.IsStableUnderBaseChange
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.Flat ∧ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType :=
  sorry

end TopologicalRing.Noetherian
