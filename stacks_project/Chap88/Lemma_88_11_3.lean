module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap87.Remark_87_21_8_Variant_for_adic_star_BaseChange

/-!
# Adic topologically finite type arrows of WAdm^{adic*} are stable under base change
-/

@[expose] public section

universe u

open TopologicalRing RingHom

namespace TopologicalRing.IsAdicStarRing

/-- Lemma 88.11.3: Consider the property `P` on arrows of `WAdm^{adic*}` defined
in Lemma 88.11.1, namely `fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType`.
Then `P` is stable under base change as defined in Formal Spaces,
Remark 87.21.8: `P (algebraMap B A)` implies `P (includeRight B A C)` for the
completed tensor product. -/
@[stacks 0GBY]
theorem isStableUnderBaseChange_isAdicHom_and_topologicallyOfFiniteType :
    IsLocalMorphismProperty.IsStableUnderBaseChange
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
        (φ : B →+* A) ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType :=
  sorry

end TopologicalRing.IsAdicStarRing
