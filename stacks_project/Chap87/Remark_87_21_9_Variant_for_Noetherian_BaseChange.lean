/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.Noetherian.BaseChange

/-!
# Stability of Noetherian adic morphism properties under completed base change

A property of morphisms of Noetherian adic rings is stable under base change
when `P (algebraMap B A)` implies that `Completed B A C` is adic Noetherian
and that `P (includeRight B A C)` holds.
-/

@[expose] public section

universe u

open Algebra.TensorProduct Algebra.TensorProduct.Completed

namespace TopologicalRing.Noetherian.IsLocalMorphismProperty

variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)

#check (TopologicalRing.Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange P : Prop)

#check (TopologicalRing.Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange.of P :
    ∀ (isAdicNoetherian :
      ∀ {A B C : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
        [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C],
        P (algebraMap B A) →
          IsAdicRing (Completed B A C) ∧ IsNoetherianRing (Completed B A C))
    (ofIncludeRight :
      ∀ {A B C : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
        [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C]
        [IsAdicRing (Completed B A C)] [IsNoetherianRing (Completed B A C)],
        P (algebraMap B A) → P (includeRight B A C)),
    IsStableUnderBaseChange P)

#check (TopologicalRing.Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange.iff P :
    IsStableUnderBaseChange P ↔
      (∀ {A B C : Type u}
          [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
          [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
          [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
          [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C],
          P (algebraMap B A) →
            IsAdicRing (Completed B A C) ∧ IsNoetherianRing (Completed B A C)) ∧
        ∀ {A B C : Type u}
          [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
          [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
          [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
          [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C]
          [IsAdicRing (Completed B A C)] [IsNoetherianRing (Completed B A C)],
          P (algebraMap B A) → P (includeRight B A C))

variable {P}
variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
variable [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
variable [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
variable [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C]

#check (TopologicalRing.Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange.isAdicRing :
    ∀ (hbc : IsStableUnderBaseChange P) (hφ : P (algebraMap B A)),
    IsAdicRing (Completed B A C))

#check (TopologicalRing.Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange.isNoetherianRing :
    ∀ (hbc : IsStableUnderBaseChange P)
    (hφ : P (algebraMap B A)), IsNoetherianRing (Completed B A C))

#check (TopologicalRing.Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange.of_includeRight :
    ∀ (hbc : IsStableUnderBaseChange P)
    [IsAdicRing (Completed B A C)] [IsNoetherianRing (Completed B A C)]
    (hφ : P (algebraMap B A)), P (includeRight B A C))

end TopologicalRing.Noetherian.IsLocalMorphismProperty
