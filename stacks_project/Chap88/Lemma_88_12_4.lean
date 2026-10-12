/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType
public import stacks_project.Chap87.«87_21_2_1_LocalizeSquare»
public import stacks_project.Chap88.Lemma_88_12_1_FiniteTypeReduction

/-!
# Taut topologically finite type maps are finite type on reductions
-/

@[expose] public section

universe u

open TopologicalRing

namespace RingHom.IsFiniteTypeOnReduction

/-- Lemma 88.12.4: Let `φ : A →+* B` be an arrow of `WAdm^count`. If `φ` is taut
and topologically of finite type, then `φ` satisfies the finite type on
reduction condition of Lemma 88.12.1. -/
@[stacks 0GC5]
theorem of_isTaut_topologicallyOfFiniteType {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
    {φ : A →+* B} (hφ : Continuous φ) (h_taut : φ.IsTaut)
    (h_tft : φ.TopologicallyOfFiniteType) :
    φ.IsFiniteTypeOnReduction :=
  sorry

end RingHom.IsFiniteTypeOnReduction
