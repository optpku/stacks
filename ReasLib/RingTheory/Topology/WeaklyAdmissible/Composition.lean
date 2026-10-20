module

public import ReasLib.RingTheory.Topology.CountablyIndexed
public import ReasLib.RingTheory.Topology.WeaklyAdmissible

/-!
# Stability under composition for morphisms of WAdm^count

A property of morphisms of countably indexed weakly admissible rings is stable
under composition when it is preserved by composition of continuous ring maps.
-/

@[expose] public section

universe u

namespace TopologicalRing

variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop)

/-- A property of morphisms of countably indexed weakly admissible rings is
stable under composition if `P φ` and `P ψ` imply `P (φ.comp ψ)` for continuous
ring maps `φ : B →+* A` and `ψ : C →+* B`. -/
def IsStableUnderComposition : Prop :=
  ∀ {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
    [CommRing C] [TopologicalSpace C] [IsWeaklyAdmissibleRing C] [IsCountablyIndexed C]
    (φ : B →+* A) (ψ : C →+* B),
    Continuous φ → Continuous ψ → P φ → P ψ → P (φ.comp ψ)

/-- Stability under composition is the implication `P φ → P ψ → P (φ.comp ψ)` for
continuous morphisms of countably indexed weakly admissible rings. -/
theorem isStableUnderComposition_iff :
    IsStableUnderComposition P ↔
      ∀ {A B C : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        [CommRing C] [TopologicalSpace C] [IsWeaklyAdmissibleRing C] [IsCountablyIndexed C]
        (φ : B →+* A) (ψ : C →+* B),
        Continuous φ → Continuous ψ → P φ → P ψ → P (φ.comp ψ) := sorry

namespace IsStableUnderComposition

variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
variable [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
variable [CommRing C] [TopologicalSpace C] [IsWeaklyAdmissibleRing C] [IsCountablyIndexed C]

/-- If `P` is stable under composition, then `P φ` and `P ψ` imply `P (φ.comp ψ)`
for continuous morphisms of countably indexed weakly admissible rings. -/
theorem comp (hP : IsStableUnderComposition P) (φ : B →+* A) (ψ : C →+* B)
    (hφcont : Continuous φ) (hψcont : Continuous ψ) (hφ : P φ) (hψ : P ψ) :
    P (φ.comp ψ) := sorry

end IsStableUnderComposition

end TopologicalRing
