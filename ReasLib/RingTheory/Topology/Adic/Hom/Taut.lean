module

public import ReasLib.RingTheory.Topology.Adic.Hom
public import ReasLib.RingTheory.Topology.Adic.Taut
public import ReasLib.Topology.Algebra.Ring.Taut

/-!
# Tautness of adic homomorphisms

A continuous adic homomorphism of pre-adic rings is taut.
-/

@[expose] public section

universe u v

namespace RingHom

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [TopologicalRing.IsPreadicRing A]
variable [CommRing B] [TopologicalSpace B] [TopologicalRing.IsPreadicRing B]

/-- A continuous adic homomorphism between pre-adic topological rings is taut. -/
@[stacks 0GXC]
theorem IsAdicHom.isTaut {φ : A →+* B} (hφ_cont : Continuous φ) (hφ : φ.IsAdicHom) :
    φ.IsTaut := sorry

end

/-- A continuous homomorphism between adic rings with finitely generated ideals of
definition is adic if and only if it is taut. -/
@[stacks 0GBS]
theorem isAdicHom_iff_isTaut {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A]
    [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdicRing B]
    (φ : A →+* B) (hcont : Continuous φ)
    (hA : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hB : ∃ J : Ideal B, J.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition J) :
    φ.IsAdicHom ↔ φ.IsTaut :=
  sorry

end RingHom
