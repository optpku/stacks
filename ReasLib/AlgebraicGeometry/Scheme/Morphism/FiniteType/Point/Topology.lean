module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point

/-!
# Topology of finite-type points

Finite-type points meet every nonempty locally closed subset and are dense in every closed
subspace of a scheme.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- Every nonempty locally closed subset of a scheme contains a finite-type point. -/
theorem nonempty_inter_finiteTypePoints
    (S : Scheme.{u}) {T : Set S} (hne : T.Nonempty) (hT : IsLocallyClosed T) :
    (T ∩ finiteTypePoints S).Nonempty := sorry

/-- The finite-type points of a scheme lying in a closed subset are dense in that subset. -/
theorem dense_finiteTypePoints_in_closed_subset
    (S : Scheme.{u}) {T : Set S} (hT : IsClosed T) :
    Dense {x : T | (x : S) ∈ finiteTypePoints S} := sorry

end AlgebraicGeometry
