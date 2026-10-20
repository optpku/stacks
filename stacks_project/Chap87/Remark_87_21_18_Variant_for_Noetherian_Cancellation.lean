/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.Noetherian.Cancellation

/-!
# Cancellation for morphisms of Noetherian adic rings

The cancellation predicate and its constructor and characterization apply to
continuous morphisms of Noetherian adic rings.
-/

@[expose] public section

universe u

open TopologicalRing

#check (TopologicalRing.Noetherian.HasCancellationProperty :
  (∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop) → Prop)

#check (TopologicalRing.Noetherian.HasCancellationProperty.of :
  ∀ (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop),
    (∀ {A B C : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
      [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
      (φ : B →+* A) (ψ : C →+* B),
      Continuous φ → Continuous ψ → P ψ → P (φ.comp ψ) → P φ) → Noetherian.HasCancellationProperty P)

#check (TopologicalRing.Noetherian.HasCancellationProperty.iff :
  ∀ (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop),
    Noetherian.HasCancellationProperty P ↔
    ∀ {A B C : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
      [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
      (φ : B →+* A) (ψ : C →+* B),
      Continuous φ → Continuous ψ → P ψ → P (φ.comp ψ) → P φ)
