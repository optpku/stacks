/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Situation_87_21_11_Composition
public import stacks_project.Chap88.Lemma_88_12_1_FiniteTypeReduction

/-!
# Finite type on reductions is stable under composition
-/

@[expose] public section

universe u

open TopologicalRing RingHom

namespace TopologicalRing

/-- Lemma 88.12.3: Consider the property `P` on arrows of `WAdm^count` defined
in Lemma 88.12.1. Then `P` is stable under composition in the sense of
Situation 87.21.11. -/
@[stacks 0GC4]
theorem isStableUnderComposition_isFiniteTypeOnReduction :
    IsStableUnderComposition
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        (φ : B →+* A) ↦ φ.IsFiniteTypeOnReduction :=
  sorry

end TopologicalRing

namespace RingHom.IsFiniteTypeOnReduction

variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
variable [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
variable [CommRing C] [TopologicalSpace C] [IsWeaklyAdmissibleRing C] [IsCountablyIndexed C]

/-- Finite type on reduction is preserved by composition of continuous morphisms
of countably indexed weakly admissible rings. -/
theorem comp {φ : B →+* A} {ψ : C →+* B} (hφcont : Continuous φ) (hψcont : Continuous ψ)
    (hφ : φ.IsFiniteTypeOnReduction) (hψ : ψ.IsFiniteTypeOnReduction) :
    (φ.comp ψ).IsFiniteTypeOnReduction :=
  sorry

end RingHom.IsFiniteTypeOnReduction
