/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.Noetherian.Composition
public import ReasLib.RingTheory.Topology.Noetherian.LocalMorphismProperty

/-!
# Stability under composition for morphisms of Noetherian adic rings

Typed compatibility checks for composition stability and its specification API.
-/

@[expose] public section

universe u

open TopologicalRing

#check (TopologicalRing.Noetherian.IsStableUnderComposition :
  (∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop) → Prop)

#check (TopologicalRing.Noetherian.isStableUnderComposition_iff :
  ∀ (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop),
    Noetherian.IsStableUnderComposition P ↔
      ∀ {A B C : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
        (φ : B →+* A) (ψ : C →+* B),
        Continuous φ → Continuous ψ → P φ → P ψ → P (φ.comp ψ))

#check (TopologicalRing.Noetherian.IsStableUnderComposition.comp :
  ∀ (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
    [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C],
    Noetherian.IsStableUnderComposition P →
    ∀ (φ : B →+* A) (ψ : C →+* B),
      Continuous φ → Continuous ψ → P φ → P ψ → P (φ.comp ψ))
