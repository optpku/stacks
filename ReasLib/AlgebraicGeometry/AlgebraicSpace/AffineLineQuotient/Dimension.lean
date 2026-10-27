/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Order
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension

/-!
# Dimension of the affine-line translation quotient

The quotient of the affine line by integer translation has étale-local dimension one
over a characteristic-zero field, but its indiscrete point space has dimension zero.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient

/-- The quotient of the affine line over a characteristic-zero field by integer
translation has dimension one at every point. -/
theorem dimensionAt_eq_one (k : Type u) [Field k] [CharZero k] (x : Points (space k)) :
    dimensionAt x = 1 :=
  sorry

/-- The point space of the affine-line translation quotient over a characteristic-zero
field has the indiscrete topology. -/
instance instIndiscreteTopology_points (k : Type u) [Field k] [CharZero k] :
    IndiscreteTopology (Points (space k)) :=
  sorry

/-- The point space of the affine-line translation quotient over a characteristic-zero
field has topological Krull dimension zero. -/
theorem topologicalKrullDim_points_eq_zero (k : Type u) [Field k] [CharZero k] :
    topologicalKrullDim (Points (space k)) = 0 :=
  sorry

/-- The point space of the affine-line translation quotient over a characteristic-zero
field has local topological Krull dimension zero at every point. -/
theorem topologicalKrullDimAt_points_eq_zero (k : Type u) [Field k] [CharZero k]
    (x : Points (space k)) : topologicalKrullDimAt x = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient
