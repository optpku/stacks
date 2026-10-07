module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_4_8_WeaklyAdmissible
public import stacks_project.Chap87.Definition_87_5_1_Taut

/-!
# Lemma 87.5.2

A continuous homomorphism of weakly admissible topological rings is taut if and
only if the closures of the extensions of weak ideals of definition of the
source form a fundamental system of weak ideals of definition of the target.
-/

@[expose] public section

open scoped Topology
open TopologicalRing
open TopologicalRing.Ideal

universe u v

namespace RingHom

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A]
variable [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B]

/-- Lemma 87.5.2: Let `φ : A →+* B` be a continuous homomorphism of weakly
admissible topological rings. Then `φ` is taut if and only if, for every weak
ideal of definition `I` of `A`, the closure of `Ideal.map φ I` is a weak ideal
of definition of `B`, and these closures are cofinal among weak ideals of
definition of `B`. -/
@[stacks 0AMY]
theorem isTaut_iff_weakIdealOfDefinition {φ : A →+* B} (hφ : Continuous φ) :
    φ.IsTaut ↔
      (∀ I : Ideal A, IsWeakIdealOfDefinition I →
          IsWeakIdealOfDefinition (Ideal.map φ I).closure) ∧
        ∀ J : Ideal B, IsWeakIdealOfDefinition J →
          ∃ I : Ideal A, IsWeakIdealOfDefinition I ∧ (Ideal.map φ I).closure ≤ J :=
  sorry

namespace IsTaut

/-- If `φ` is a continuous taut homomorphism of weakly admissible topological
rings, then the closure of the extension of every weak ideal of definition of
the source is a weak ideal of definition of the target. -/
theorem isWeakIdealOfDefinition_closure_map {φ : A →+* B} (hφ : Continuous φ)
    (htaut : φ.IsTaut) {I : Ideal A} (hI : IsWeakIdealOfDefinition I) :
    IsWeakIdealOfDefinition (Ideal.map φ I).closure :=
  sorry

/-- If `φ` is a continuous taut homomorphism of weakly admissible topological
rings, then every weak ideal of definition of the target contains the closure of
the extension of some weak ideal of definition of the source. -/
theorem exists_weakIdealOfDefinition_closure_map_le {φ : A →+* B}
    (hφ : Continuous φ) (htaut : φ.IsTaut) {J : Ideal B}
    (hJ : IsWeakIdealOfDefinition J) :
    ∃ I : Ideal A, IsWeakIdealOfDefinition I ∧ (Ideal.map φ I).closure ≤ J :=
  sorry

end IsTaut

/-- A continuous homomorphism of weakly admissible topological rings is taut if
and only if the closures of the extensions of weak ideals of definition of the
source are themselves weak ideals of definition and form a neighborhood basis
of `0` in the target. -/
theorem isTaut_iff_hasBasis_weakIdealOfDefinition {φ : A →+* B}
    (hφ : Continuous φ) :
    φ.IsTaut ↔
      (∀ I : Ideal A, IsWeakIdealOfDefinition I →
          IsWeakIdealOfDefinition (Ideal.map φ I).closure) ∧
        (nhds (0 : B)).HasBasis (fun I : Ideal A ↦ IsWeakIdealOfDefinition I)
          (fun I ↦ ((Ideal.map φ I).closure : Set B)) :=
  sorry

end RingHom
