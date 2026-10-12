/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Situation_87_21_2_MorphismProperty
public import stacks_project.Chap87.Situation_87_21_6_Completed

/-!
# Stability of morphism properties under completed base change

A property of morphisms of countably indexed weakly admissible rings is stable
under base change when it passes from `algebraMap B A` to
`includeRight B A C : C →+* Completed B A C`.
-/

@[expose] public section

universe u

open Algebra.TensorProduct.Completed

namespace TopologicalRing

variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop)

namespace IsLocalMorphismProperty

/-- A morphism property of countably indexed weakly admissible rings is stable
under base change if `P (algebraMap B A)` implies
`P (includeRight B A C)` for algebras `A` and `C` over `B`. -/
def IsStableUnderBaseChange : Prop :=
  ∀ {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
    [CommRing C] [TopologicalSpace C] [IsWeaklyAdmissibleRing C] [IsCountablyIndexed C]
    [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C],
    P (algebraMap B A) → P (includeRight B A C)

namespace IsStableUnderBaseChange

/-- A morphism property of `WAdm^count` is stable under base change iff it
passes from `algebraMap B A` to `includeRight B A C`. -/
theorem iff :
    IsStableUnderBaseChange P ↔
      ∀ {A B C : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        [CommRing C] [TopologicalSpace C] [IsWeaklyAdmissibleRing C] [IsCountablyIndexed C]
        [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C],
        P (algebraMap B A) → P (includeRight B A C) := sorry

variable {P}
variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
variable [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
variable [CommRing C] [TopologicalSpace C] [IsWeaklyAdmissibleRing C] [IsCountablyIndexed C]
variable [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C]

/-- Stability under base change applies to the canonical inclusion
`includeRight B A C`. -/
theorem of_includeRight (hP : IsStableUnderBaseChange P) (hφ : P (algebraMap B A)) :
    P (includeRight B A C) := sorry

end IsStableUnderBaseChange

end IsLocalMorphismProperty

end TopologicalRing
