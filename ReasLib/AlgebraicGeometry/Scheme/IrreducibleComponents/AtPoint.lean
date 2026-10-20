module

public import Mathlib.AlgebraicGeometry.Stalk
public import ReasLib.Topology.IrreducibleComponents.AtPoint

/-!
# Minimal primes of scheme stalks and irreducible components through a point
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- The number of minimal primes of a scheme stalk equals the number of irreducible
components of the scheme containing the point. -/
theorem encard_minimalPrimes_stalk_eq_irreducibleComponentsAt
    (X : Scheme.{u}) (x : X) :
    (minimalPrimes (X.presheaf.stalk x)).encard =
      (TopologicalSpace.irreducibleComponentsAt x).encard :=
  sorry

end AlgebraicGeometry.Scheme
