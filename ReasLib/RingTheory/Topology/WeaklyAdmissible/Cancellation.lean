/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.CountablyIndexed
public import ReasLib.RingTheory.Topology.WeaklyAdmissible

/-!
# Cancellation for morphisms of countably indexed weakly admissible rings

A property of morphisms of countably indexed weakly admissible rings has the
cancellation property when `P ψ` and `P (φ.comp ψ)` imply `P φ` for continuous
ring maps `φ : B →+* A` and `ψ : C →+* B`.
-/

@[expose] public section

universe u

namespace TopologicalRing

variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop)

/-- A property of morphisms of countably indexed weakly admissible rings has the
cancellation property if `P ψ` and `P (φ.comp ψ)` imply `P φ`. -/
structure HasCancellationProperty : Prop where
  /-- Given continuous `φ : B →+* A` and `ψ : C →+* B`, `P ψ` and `P (φ.comp ψ)`
  imply `P φ`. -/
  of_comp {A B C : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
      [CommRing C] [TopologicalSpace C] [IsWeaklyAdmissibleRing C] [IsCountablyIndexed C]
      (φ : B →+* A) (ψ : C →+* B) (hφ : Continuous φ) (hψ : Continuous ψ)
      (hψP : P ψ) (hcomp : P (φ.comp ψ)) : P φ

namespace HasCancellationProperty

/-- The cancellation implication gives the cancellation property for continuous
morphisms of countably indexed weakly admissible rings. -/
def of
    (of_comp :
      ∀ {A B C : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        [CommRing C] [TopologicalSpace C] [IsWeaklyAdmissibleRing C] [IsCountablyIndexed C]
        (φ : B →+* A) (ψ : C →+* B),
        Continuous φ → Continuous ψ → P ψ → P (φ.comp ψ) → P φ) :
    HasCancellationProperty P where
  of_comp := of_comp

/-- A morphism property of `WAdm^count` has the cancellation property iff
`P ψ` and `P (φ.comp ψ)` imply `P φ` for continuous maps. -/
theorem iff :
    HasCancellationProperty P ↔
      ∀ {A B C : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        [CommRing C] [TopologicalSpace C] [IsWeaklyAdmissibleRing C] [IsCountablyIndexed C]
        (φ : B →+* A) (ψ : C →+* B),
        Continuous φ → Continuous ψ → P ψ → P (φ.comp ψ) → P φ := sorry

end HasCancellationProperty

end TopologicalRing
