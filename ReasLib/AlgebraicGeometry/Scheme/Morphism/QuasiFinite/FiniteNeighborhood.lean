module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

@[expose] public section

/-!
# Finite neighborhoods from finite fibers

This module gives a criterion for a proper morphism to become finite over an open neighborhood.
-/

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A proper morphism with finite point-set fiber over a point becomes finite after restriction to
an open neighborhood of that point. -/
theorem exists_isFinite_morphismRestrict_of_finite_preimage_singleton
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s : S)
    (hs : Set.Finite (f ⁻¹' ({s} : Set S))) :
    ∃ V : S.Opens, s ∈ V ∧ IsFinite (f ∣_ V) := sorry

end AlgebraicGeometry.Scheme.Hom
