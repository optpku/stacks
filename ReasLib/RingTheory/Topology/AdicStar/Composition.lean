/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.AdicStar

/-!
# Composition stability for continuous homomorphisms of adic-star rings

A property of continuous homomorphisms of adic-star rings is stable under
composition when it holds for composites of homomorphisms having the property.
-/

@[expose] public section

universe u

namespace TopologicalRing.IsAdicStarRing

variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop)

/-- A property of continuous homomorphisms of adic-star rings is stable under
composition if `P φ` and `P ψ` imply `P (φ.comp ψ)`. -/
def IsStableUnderComposition : Prop :=
  ∀ {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
    [CommRing C] [TopologicalSpace C] [IsAdicStarRing C]
    (φ : B →+* A) (ψ : C →+* B),
    Continuous φ → Continuous ψ → P φ → P ψ → P (φ.comp ψ)

/-- Stability under composition is equivalent to preservation of the property
under composition of continuous homomorphisms of adic-star rings. -/
theorem isStableUnderComposition_iff :
    IsStableUnderComposition P ↔
      ∀ {A B C : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
        [CommRing C] [TopologicalSpace C] [IsAdicStarRing C]
        (φ : B →+* A) (ψ : C →+* B),
        Continuous φ → Continuous ψ → P φ → P ψ → P (φ.comp ψ) := sorry

namespace IsStableUnderComposition

variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
variable [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
variable [CommRing C] [TopologicalSpace C] [IsAdicStarRing C]

/-- A composition-stable property of continuous homomorphisms of adic-star
rings holds for the composite of two homomorphisms having the property. -/
theorem comp (hP : IsStableUnderComposition P) (φ : B →+* A) (ψ : C →+* B)
    (hφcont : Continuous φ) (hψcont : Continuous ψ) (hφ : P φ) (hψ : P ψ) :
    P (φ.comp ψ) := sorry

end IsStableUnderComposition

end TopologicalRing.IsAdicStarRing
