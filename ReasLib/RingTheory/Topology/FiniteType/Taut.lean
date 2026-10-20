module

public import Mathlib.Data.List.TFAE
public import ReasLib.Topology.Algebra.Ring.Taut
public import ReasLib.RingTheory.Topology.FiniteType
public import ReasLib.RingTheory.RestrictedPowerSeries.Quotient
public import ReasLib.RingTheory.Topology.FiniteType.WeakIdealQuotients
public import ReasLib.RingTheory.Topology.LocalMorphismProperty

/-!
# Taut topologically finite type arrows of WAdm^count

A continuous arrow of countably indexed weakly admissible rings is taut and
topologically of finite type if and only if its weak-ideal reductions are of
finite type, equivalently if the target is a closed quotient of a finite-variable
restricted power series algebra. This property satisfies étale-completion
ascent, faithfully flat descent, and finite-product locality.
-/

@[expose] public section

open TopologicalRing
open TopologicalRing.Ideal

universe u

namespace RingHom

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
variable [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]

/-- For a continuous homomorphism of countably indexed weakly admissible rings,
tautness with finite type on every weak-ideal quotient, tautness with finite type
on a cofinal weak-ideal system, taut topological finite type, and presentation
as a closed quotient of a finite-variable restricted power series algebra are
equivalent. -/
theorem taut_topologicallyOfFiniteType_tfae {φ : B →+* A} (hφ : Continuous φ) :
    List.TFAE
      [φ.IsTaut ∧ φ.IsFiniteTypeOnWeakIdealQuotients,
        φ.IsTaut ∧ φ.IsFiniteTypeOnCofinalWeakIdealQuotients,
        φ.IsTaut ∧ φ.TopologicallyOfFiniteType,
        φ.IsClosedQuotientOfRestrictedPowerSeries] :=
  sorry

/-- Tautness together with finite type on every weak-ideal quotient is equivalent
to tautness together with topological finite type. -/
theorem isTaut_and_isFiniteTypeOnWeakIdealQuotients_iff {φ : B →+* A}
    (hφ : Continuous φ) :
    (φ.IsTaut ∧ φ.IsFiniteTypeOnWeakIdealQuotients) ↔
      φ.IsTaut ∧ φ.TopologicallyOfFiniteType :=
  (taut_topologicallyOfFiniteType_tfae hφ).out 0 2

/-- Tautness together with finite type along a cofinal weak-ideal system is
equivalent to tautness together with topological finite type. -/
theorem isTaut_and_isFiniteTypeOnCofinalWeakIdealQuotients_iff {φ : B →+* A}
    (hφ : Continuous φ) :
    (φ.IsTaut ∧ φ.IsFiniteTypeOnCofinalWeakIdealQuotients) ↔
      φ.IsTaut ∧ φ.TopologicallyOfFiniteType :=
  (taut_topologicallyOfFiniteType_tfae hφ).out 1 2

/-- Tautness together with topological finite type is equivalent to `A` being a
closed quotient of `RestrictedPowerSeries (Fin n) B` as a topological `B`-algebra. -/
theorem taut_finiteType_iff_closedQuotient
    {φ : B →+* A} (hφ : Continuous φ) :
    (φ.IsTaut ∧ φ.TopologicallyOfFiniteType) ↔
      φ.IsClosedQuotientOfRestrictedPowerSeries :=
  (taut_topologicallyOfFiniteType_tfae hφ).out 2 3

end RingHom

namespace TopologicalRing

/-- Taut topological finite type is stable under étale weak-ideal completion
squares, descends along such squares with faithfully flat target map, and is
stable under finite products of targets. -/
theorem isLocalMorphismProperty_isTaut_and_topologicallyOfFiniteType :
    IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        (φ : B →+* A) ↦ φ.IsTaut ∧ φ.TopologicallyOfFiniteType :=
  sorry

end TopologicalRing
