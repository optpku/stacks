/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.Noetherian.BaseChange

/-!
# Relative completed base change for Noetherian adic rings

Typed compatibility checks for the relative completed-base-change predicate
and its specification API.
-/

@[expose] public section

universe u

open Algebra.TensorProduct Algebra.TensorProduct.Completed

namespace TopologicalRing.Noetherian.IsLocalMorphismProperty

#check (TopologicalRing.Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy :
  ∀ (P Q : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop), Prop)

#check (TopologicalRing.Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy.of :
  ∀ (P Q : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)
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
        P (algebraMap B A) → Q (algebraMap B C) → P (includeRight B A C)),
    IsStableUnderBaseChangeBy P Q)

#check (TopologicalRing.Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy.iff :
  ∀ (P Q : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop),
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
            P (includeRight B A C))

#check (TopologicalRing.Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy.spec :
  ∀ {P Q : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop}
    {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
    [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
    [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C]
    (hbc : IsStableUnderBaseChangeBy P Q)
    (hφ : P (algebraMap B A)) (hψ : Q (algebraMap B C)),
    IsAdicRing (Completed B A C) ∧ IsNoetherianRing (Completed B A C) ∧
      ∀ [IsAdicRing (Completed B A C)] [IsNoetherianRing (Completed B A C)],
        P (includeRight B A C))

#check (TopologicalRing.Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy.isAdicRing :
  ∀ {P Q : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop}
    {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
    [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
    [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C]
    (hbc : IsStableUnderBaseChangeBy P Q)
    (hφ : P (algebraMap B A)) (hψ : Q (algebraMap B C)),
    IsAdicRing (Completed B A C))

#check (TopologicalRing.Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy.isNoetherianRing :
  ∀ {P Q : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop}
    {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
    [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
    [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C]
    (hbc : IsStableUnderBaseChangeBy P Q)
    (hφ : P (algebraMap B A)) (hψ : Q (algebraMap B C)),
    IsNoetherianRing (Completed B A C))

#check (TopologicalRing.Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy.of_includeRight :
  ∀ {P Q : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop}
    {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
    [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
    [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C]
    (hbc : IsStableUnderBaseChangeBy P Q)
    [IsAdicRing (Completed B A C)] [IsNoetherianRing (Completed B A C)]
    (hφ : P (algebraMap B A)) (hψ : Q (algebraMap B C)),
    P (includeRight B A C))

end TopologicalRing.Noetherian.IsLocalMorphismProperty
