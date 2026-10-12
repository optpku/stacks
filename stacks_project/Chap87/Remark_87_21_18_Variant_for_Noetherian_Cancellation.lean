/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.Topology.Adic.Complete

/-!
# Cancellation for morphisms of Noetherian adic rings

A property of morphisms of Noetherian adic rings has the cancellation
property when `P ψ` and `P (φ.comp ψ)` imply `P φ` for continuous ring maps
`φ : B →+* A` and `ψ : C →+* B`.
-/

@[expose] public section

universe u

namespace TopologicalRing.Noetherian

variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)

/-- A property of morphisms of Noetherian adic rings has the cancellation
property if `P ψ` and `P (φ.comp ψ)` imply `P φ`. -/
structure HasCancellationProperty : Prop where
  /-- Given continuous `φ : B →+* A` and `ψ : C →+* B`, `P ψ` and `P (φ.comp ψ)`
  imply `P φ`. -/
  of_comp {A B C : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
      [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
      (φ : B →+* A) (ψ : C →+* B) (hφ : Continuous φ) (hψ : Continuous ψ)
      (hψP : P ψ) (hcomp : P (φ.comp ψ)) : P φ

namespace HasCancellationProperty

/-- Package the cancellation implication into a cancellation property. -/
def of
    (of_comp :
      ∀ {A B C : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
        (φ : B →+* A) (ψ : C →+* B),
        Continuous φ → Continuous ψ → P ψ → P (φ.comp ψ) → P φ) :
    HasCancellationProperty P where
  of_comp := of_comp

/-- A morphism property of `WAdm^Noeth` has the cancellation property iff
`P ψ` and `P (φ.comp ψ)` imply `P φ` for continuous maps. -/
theorem iff :
    HasCancellationProperty P ↔
      ∀ {A B C : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
        (φ : B →+* A) (ψ : C →+* B),
        Continuous φ → Continuous ψ → P ψ → P (φ.comp ψ) → P φ := sorry

end HasCancellationProperty

end TopologicalRing.Noetherian
