/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Remark_87_21_5_Variant_for_Noetherian_MorphismProperty

/-!
# Stability under composition for morphisms of WAdm^Noeth

A property of morphisms of Noetherian adic rings is stable under composition
when it is preserved by composition of continuous ring maps.
-/

@[expose] public section

universe u

namespace TopologicalRing.Noetherian

variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)

/-- A property of morphisms of Noetherian adic rings is stable under
composition if `P φ` and `P ψ` imply `P (φ.comp ψ)` for continuous ring maps
`φ : B →+* A` and `ψ : C →+* B`. -/
def IsStableUnderComposition : Prop :=
  ∀ {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
    [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
    (φ : B →+* A) (ψ : C →+* B),
    Continuous φ → Continuous ψ → P φ → P ψ → P (φ.comp ψ)

/-- Stability under composition is the implication `P φ → P ψ → P (φ.comp ψ)`
for continuous morphisms of Noetherian adic rings. -/
theorem isStableUnderComposition_iff :
    IsStableUnderComposition P ↔
      ∀ {A B C : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
        (φ : B →+* A) (ψ : C →+* B),
        Continuous φ → Continuous ψ → P φ → P ψ → P (φ.comp ψ) := sorry

namespace IsStableUnderComposition

variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
variable [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
variable [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]

/-- If `P` is stable under composition, then `P φ` and `P ψ` imply
`P (φ.comp ψ)` for continuous morphisms of Noetherian adic rings. -/
theorem comp (hP : IsStableUnderComposition P) (φ : B →+* A) (ψ : C →+* B)
    (hφcont : Continuous φ) (hψcont : Continuous ψ) (hφ : P φ) (hψ : P ψ) :
    P (φ.comp ψ) := sorry

end IsStableUnderComposition

end TopologicalRing.Noetherian
