module

public import ReasLib.RingTheory.Topology.FiniteType.Taut

/-!
# Taut topologically finite type homomorphisms with admissible source

For an admissible source, taut topological finite type is equivalent to tautness
and finite type on a single ideal-of-definition quotient.
-/

@[expose] public section

open TopologicalRing
open TopologicalRing.Ideal

universe u

namespace RingHom

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
variable [CommRing B] [TopologicalSpace B] [IsAdmissibleRing B] [IsCountablyIndexed B]

/-- For a continuous homomorphism of countably indexed weakly admissible rings
with admissible source, tautness with finite type on every weak-ideal quotient,
tautness with finite type on a cofinal weak-ideal system, taut topological finite
type, presentation as a closed quotient of a finite-variable restricted power
series algebra, and tautness with finite type on some ideal-of-definition
quotient are equivalent. -/
theorem taut_topologicallyOfFiniteType_tfae_of_isAdmissibleRing {φ : B →+* A}
    (hφ : Continuous φ) :
    List.TFAE
      [φ.IsTaut ∧ φ.IsFiniteTypeOnWeakIdealQuotients,
        φ.IsTaut ∧ φ.IsFiniteTypeOnCofinalWeakIdealQuotients,
        φ.IsTaut ∧ φ.TopologicallyOfFiniteType,
        φ.IsClosedQuotientOfRestrictedPowerSeries,
        φ.IsTaut ∧ φ.IsFiniteTypeOnSomeIdealOfDefinition] :=
  sorry

/-- Tautness together with finite type on some ideal-of-definition quotient is
equivalent to tautness together with topological finite type. -/
theorem isTaut_and_isFiniteTypeOnSomeIdealOfDefinition_iff {φ : B →+* A}
    (hφ : Continuous φ) :
    (φ.IsTaut ∧ φ.IsFiniteTypeOnSomeIdealOfDefinition) ↔
      φ.IsTaut ∧ φ.TopologicallyOfFiniteType :=
  (taut_topologicallyOfFiniteType_tfae_of_isAdmissibleRing hφ).out 4 2

/-- Tautness together with finite type on every weak-ideal quotient is equivalent
to tautness together with finite type on some ideal-of-definition quotient. -/
theorem taut_finiteTypeQuotients_iff_someIdealOfDefinition
    {φ : B →+* A} (hφ : Continuous φ) :
    (φ.IsTaut ∧ φ.IsFiniteTypeOnWeakIdealQuotients) ↔
      φ.IsTaut ∧ φ.IsFiniteTypeOnSomeIdealOfDefinition :=
  (taut_topologicallyOfFiniteType_tfae_of_isAdmissibleRing hφ).out 0 4

end RingHom
