/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Situation_87_21_6_BaseChange
public import stacks_project.Chap88.Lemma_88_12_1_FiniteTypeReduction

/-!
# Finite type on reductions is stable under completed base change
-/

@[expose] public section

universe u

open TopologicalRing RingHom

namespace TopologicalRing

/-- Lemma 88.12.2: Consider the property `P` on arrows of `WAdm^count` defined
in Lemma 88.12.1. Then `P` is stable under base change in the sense of
Situation 87.21.6. -/
@[stacks 0GC3]
theorem isStableUnderBaseChange_isFiniteTypeOnReduction :
    IsLocalMorphismProperty.IsStableUnderBaseChange
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        (φ : B →+* A) ↦ φ.IsFiniteTypeOnReduction :=
  sorry

end TopologicalRing
