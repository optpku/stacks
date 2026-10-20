/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.WeaklyAdmissible
public import ReasLib.Topology.Algebra.Ring.Taut
public import ReasLib.RingTheory.Topology.TopologicalNilradical

/-!
# Taut ascent of weakly pre-admissible rings
-/

@[expose] public section

universe u v

namespace TopologicalRing.Ideal.IsWeakIdealOfDefinition

/-- The closure of the extension of a weak ideal of definition along a continuous
taut homomorphism is a weak ideal of definition. -/
theorem map_closure_of_isTaut {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) {I : Ideal A}
    (hI : IsWeakIdealOfDefinition I) :
    IsWeakIdealOfDefinition (Ideal.map φ I).closure := sorry

end TopologicalRing.Ideal.IsWeakIdealOfDefinition

namespace RingHom.IsTaut

/-- A continuous taut homomorphism carries a weakly pre-admissible source ring to
a weakly pre-admissible target ring. -/
theorem isWeaklyPreadmissibleRing {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [TopologicalRing.IsWeaklyPreadmissibleRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) :
    TopologicalRing.IsWeaklyPreadmissibleRing B := sorry

end RingHom.IsTaut

open scoped Topology
open TopologicalRing
open TopologicalRing.Ideal

namespace RingHom

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A]
variable [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B]

/-- A continuous homomorphism of weakly admissible topological rings is taut if
and only if the closures of extended weak ideals of definition are weak ideals
of definition and are cofinal among the target's weak ideals of definition. -/
theorem isTaut_iff_weakIdealOfDefinition {φ : A →+* B} (hφ : Continuous φ) :
    φ.IsTaut ↔
      (∀ I : Ideal A, IsWeakIdealOfDefinition I →
          IsWeakIdealOfDefinition (Ideal.map φ I).closure) ∧
        ∀ J : Ideal B, IsWeakIdealOfDefinition J →
          ∃ I : Ideal A, IsWeakIdealOfDefinition I ∧ (Ideal.map φ I).closure ≤ J :=
  sorry

namespace IsTaut

/-- Every weak ideal of definition in the target of a continuous taut
homomorphism of weakly admissible topological rings contains the closure of the
extension of a weak ideal of definition of the source. -/
theorem exists_weakIdealOfDefinition_closure_map_le {φ : A →+* B}
    (hφ : Continuous φ) (htaut : φ.IsTaut) {J : Ideal B}
    (hJ : IsWeakIdealOfDefinition J) :
    ∃ I : Ideal A, IsWeakIdealOfDefinition I ∧ (Ideal.map φ I).closure ≤ J :=
  ((isTaut_iff_weakIdealOfDefinition hφ).mp htaut).2 J hJ

end IsTaut

/-- A continuous homomorphism of weakly admissible topological rings is taut if
and only if the closures of extended weak ideals of definition are weak ideals
of definition and form a neighborhood basis at zero in the target. -/
theorem isTaut_iff_hasBasis_weakIdealOfDefinition {φ : A →+* B}
    (hφ : Continuous φ) :
    φ.IsTaut ↔
      (∀ I : Ideal A, IsWeakIdealOfDefinition I →
          IsWeakIdealOfDefinition (Ideal.map φ I).closure) ∧
        (nhds (0 : B)).HasBasis (fun I : Ideal A ↦ IsWeakIdealOfDefinition I)
          (fun I ↦ ((Ideal.map φ I).closure : Set B)) :=
  sorry

end RingHom
