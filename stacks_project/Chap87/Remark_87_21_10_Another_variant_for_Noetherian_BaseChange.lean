/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Algebra.Algebra
public import stacks_project.Chap87.Lemma_87_5_6_CompletedRing
public import stacks_project.Chap87.Remark_87_21_5_Variant_for_Noetherian_MorphismProperty

/-!
# Stability of Noetherian adic morphism properties under completed base change by Q

A property `P` of morphisms of Noetherian adic rings is stable under base
change by a property `Q` when `P (algebraMap B A)` and `Q (algebraMap B C)`
imply that `Completed B A C` is adic Noetherian and that
`P (includeRight B A C)` holds.
-/

@[expose] public section

universe u

open Algebra.TensorProduct Algebra.TensorProduct.Completed

namespace TopologicalRing.Noetherian.IsLocalMorphismProperty

variable (P Q : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)

/-- A morphism property of Noetherian adic rings is stable under base change
by `Q` if `P (algebraMap B A)` and `Q (algebraMap B C)` imply that
`Completed B A C` is adic Noetherian and that `P (includeRight B A C)`
holds. -/
structure IsStableUnderBaseChangeBy : Prop where
  /-- If `P (algebraMap B A)` and `Q (algebraMap B C)`, then `Completed B A C`
  is an adic Noetherian ring. -/
  isAdicNoetherian :
    ∀ {A B C : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
      [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
      [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C],
      P (algebraMap B A) → Q (algebraMap B C) →
        IsAdicRing (Completed B A C) ∧ IsNoetherianRing (Completed B A C)
  /-- If `P (algebraMap B A)`, `Q (algebraMap B C)`, and `Completed B A C` is
  adic Noetherian, then `P (includeRight B A C)`. -/
  ofIncludeRight :
    ∀ {A B C : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
      [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
      [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C]
      [IsAdicRing (Completed B A C)] [IsNoetherianRing (Completed B A C)],
      P (algebraMap B A) → Q (algebraMap B C) → P (includeRight B A C)

namespace IsStableUnderBaseChangeBy

/-- Package the adic-Noetherian conclusion and the `includeRight` transfer
into stability of `P` under base change by `Q`. -/
def of
    (isAdicNoetherian :
      ∀ {A B C : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
        [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C],
        P (algebraMap B A) → Q (algebraMap B C) →
          IsAdicRing (Completed B A C) ∧ IsNoetherianRing (Completed B A C))
    (ofIncludeRight :
      ∀ {A B C : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
        [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C]
        [IsAdicRing (Completed B A C)] [IsNoetherianRing (Completed B A C)],
        P (algebraMap B A) → Q (algebraMap B C) → P (includeRight B A C)) :
    IsStableUnderBaseChangeBy P Q where
  isAdicNoetherian := isAdicNoetherian
  ofIncludeRight := ofIncludeRight

/-- A morphism property of `WAdm^Noeth` is stable under base change by `Q`
iff `P (algebraMap B A)` and `Q (algebraMap B C)` imply that
`Completed B A C` is adic Noetherian and that `P (includeRight B A C)`
holds. -/
theorem iff :
    IsStableUnderBaseChangeBy P Q ↔
      (∀ {A B C : Type u}
          [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
          [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
          [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
          [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C],
          P (algebraMap B A) → Q (algebraMap B C) →
            IsAdicRing (Completed B A C) ∧ IsNoetherianRing (Completed B A C)) ∧
        ∀ {A B C : Type u}
          [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
          [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
          [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
          [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C]
          [IsAdicRing (Completed B A C)] [IsNoetherianRing (Completed B A C)],
          P (algebraMap B A) → Q (algebraMap B C) →
            P (includeRight B A C) := sorry

variable {P Q}
variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
variable [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
variable [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
variable [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C]

/-- Stability of `P` under base change by `Q` applied to `algebraMap B A` and
`algebraMap B C` yields that `Completed B A C` is adic Noetherian and that
`P (includeRight B A C)` holds once those instances are available. -/
theorem spec (hbc : IsStableUnderBaseChangeBy P Q)
    (hφ : P (algebraMap B A)) (hψ : Q (algebraMap B C)) :
    IsAdicRing (Completed B A C) ∧ IsNoetherianRing (Completed B A C) ∧
      ∀ [IsAdicRing (Completed B A C)] [IsNoetherianRing (Completed B A C)],
        P (includeRight B A C) := sorry

/-- Stability of `P` under base change by `Q` implies that `Completed B A C`
is adic. -/
theorem isAdicRing (hbc : IsStableUnderBaseChangeBy P Q)
    (hφ : P (algebraMap B A)) (hψ : Q (algebraMap B C)) :
    IsAdicRing (Completed B A C) := sorry

/-- Stability of `P` under base change by `Q` implies that `Completed B A C`
is Noetherian. -/
theorem isNoetherianRing (hbc : IsStableUnderBaseChangeBy P Q)
    (hφ : P (algebraMap B A)) (hψ : Q (algebraMap B C)) :
    IsNoetherianRing (Completed B A C) := sorry

/-- Stability of `P` under base change by `Q` applies to the canonical
inclusion `includeRight B A C`. -/
theorem of_includeRight (hbc : IsStableUnderBaseChangeBy P Q)
    [IsAdicRing (Completed B A C)] [IsNoetherianRing (Completed B A C)]
    (hφ : P (algebraMap B A)) (hψ : Q (algebraMap B C)) :
    P (includeRight B A C) := sorry

end IsStableUnderBaseChangeBy

end TopologicalRing.Noetherian.IsLocalMorphismProperty
