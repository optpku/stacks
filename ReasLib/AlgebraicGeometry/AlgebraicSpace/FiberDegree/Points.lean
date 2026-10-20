module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiberDegree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import Mathlib.Data.Set.Card

/-!
# Point-fibre cardinality of universally bounded morphisms

A uniform bound on field-valued fibre degrees of a morphism from a scheme to an
algebraic space bounds the number of points in each fibre of `|U| → |X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The integer bounding field-valued fibre degrees also bounds the number of points in
each fibre of the induced map `|U| → |X|`. -/
theorem degreesOfFibresBoundedBy.mapOfOver_fibre_encard_le
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (f : ofOver U ⟶ X)
    {n : ℕ} (hf : degreesOfFibresBoundedBy f n) (x : Points X) :
    (Points.mapOfOver f ⁻¹' {x}).encard ≤ n :=
  sorry

/-- A morphism from a scheme to an algebraic space with universally bounded fibres has
a uniform finite bound on the cardinalities of the fibres of its map on points. -/
@[stacks 03JQ]
theorem exists_mapOfOver_fibre_encard_le_of_universallyBoundedFibres
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X)
    (hφ : universallyBoundedFibres φ) :
    ∃ n : ℕ, ∀ x : Points X, (Points.mapOfOver φ ⁻¹' {x}).encard ≤ n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
