module

public import stacks_project.Chap87.Remark_87_21_4_Variant_for_adic_star_AdicStarRing

/-!
# Stability under composition for morphisms of WAdm^{adic*}

A property of morphisms of adic rings with a finitely generated ideal of
definition is stable under composition when it is preserved by composition of
continuous ring maps.
-/

@[expose] public section

universe u

namespace TopologicalRing.IsAdicStarRing

variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop)

/-- A property of morphisms of `WAdm^{adic*}` is stable under composition if
`P φ` and `P ψ` imply `P (φ.comp ψ)` for continuous ring maps `φ : B →+* A`
and `ψ : C →+* B`. -/
def IsStableUnderComposition : Prop :=
  ∀ {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
    [CommRing C] [TopologicalSpace C] [IsAdicStarRing C]
    (φ : B →+* A) (ψ : C →+* B),
    Continuous φ → Continuous ψ → P φ → P ψ → P (φ.comp ψ)

/-- Stability under composition is the implication `P φ → P ψ → P (φ.comp ψ)`
for continuous morphisms of `WAdm^{adic*}`. -/
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

/-- If `P` is stable under composition, then `P φ` and `P ψ` imply
`P (φ.comp ψ)` for continuous morphisms of `WAdm^{adic*}`. -/
theorem comp (hP : IsStableUnderComposition P) (φ : B →+* A) (ψ : C →+* B)
    (hφcont : Continuous φ) (hψcont : Continuous ψ) (hφ : P φ) (hψ : P ψ) :
    P (φ.comp ψ) := sorry

end IsStableUnderComposition

end TopologicalRing.IsAdicStarRing
