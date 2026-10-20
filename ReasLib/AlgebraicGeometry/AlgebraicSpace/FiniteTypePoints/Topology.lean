module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteTypePoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Topology of finite-type points of algebraic spaces

Finite-type points meet every nonempty locally closed subset and are dense in
every closed subspace of an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every nonempty locally closed subset of the points of an algebraic space
contains a finite-type point. -/
theorem nonempty_inter_finiteTypePoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    {T : Set (Points X)} (hne : T.Nonempty) (hT : IsLocallyClosed T) :
    (T ∩ finiteTypePoints X).Nonempty :=
  sorry

/-- The finite-type points of an algebraic space lying in a closed subset are
dense in that subset. -/
theorem dense_finiteTypePoints_in_closed_subset {S : Scheme.{u}}
    (X : AlgebraicSpace S) {T : Set (Points X)} (hT : IsClosed T) :
    Dense (setOf fun (x : T) ↦ (x : Points X) ∈ finiteTypePoints X) :=
  sorry

/-- The closure of the finite-type points of an algebraic space inside a closed
subset `T` is `T`. -/
theorem closure_inter_finiteTypePoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    {T : Set (Points X)} (hT : IsClosed T) :
    closure (T ∩ finiteTypePoints X) = T :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
